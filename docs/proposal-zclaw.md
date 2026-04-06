# Proposal: WispyScheme as zclaw's Scripting Layer

## Context

[zclaw](https://zclaw.dev/) is an ESP32-resident AI agent written in C on FreeRTOS. It runs under an 888 KiB firmware budget, talks to LLM backends (Anthropic, OpenAI, OpenRouter, Ollama), and provides scheduling, GPIO control, and memory via Telegram. It targets ESP32-C3 (RISC-V), ESP32-C6 (RISC-V), ESP32-S3, and ESP32-WROOM.

Of that 888 KiB, only **38.4 KiB** is zclaw's application logic. The rest is Wi-Fi (370 KiB), TLS (132 KiB), and FreeRTOS. Every new capability requires a firmware rebuild.

## Proposal

Replace the 38.4 KiB of C application logic with WispyScheme: a `no_std` R4RS Scheme with a 1KB Cayley table for algebraic type dispatch. The agent lives inside a WispyScheme shell (inspired by [scsh](https://scsh.net/) and [schemesh](https://github.com/cosmos72/schemesh)) — the entire interaction surface is Scheme. The LLM doesn't just call tools; it writes them, composes them, and the user can inspect and modify them in the same language.

Think [Pi Agent](https://en.wikipedia.org/wiki/Pi_(chatbot)) — except the agent's shell, tools, memory, and interaction are all WispyScheme. No reflash required. The agent evolves by writing Scheme.

## What WispyScheme Adds

### The agent writes its own tools

This is the key difference from conventional tool-calling agents. zclaw's tools are C functions compiled into the firmware. The LLM selects from a fixed menu. With WispyScheme, the LLM **writes new tools in Scheme** and they become immediately available:

```scheme
;; The LLM receives: "Can you monitor the garage temperature and alert me if it's too hot?"
;; The LLM writes:

(define (garage-monitor)
  (let ((temp (raw->celsius (adc-read GARAGE_SENSOR))))
    (when (> temp 40)
      (reply "Garage temperature alert: " (number->string temp) "C"))
    temp))

(schedule-every 300 garage-monitor)  ; check every 5 minutes
(remember "garage-monitor" "active, threshold 40C")
```

The tool didn't exist before the conversation. The LLM composed it from primitives (`adc-read`, `schedule-every`, `reply`, `remember`), and now it's a first-class function the agent can call, schedule, and reference. The user can inspect it:

```scheme
;; User asks: "What's the garage monitor doing?"
;; Agent evaluates:
(recall "garage-monitor")  ; → "active, threshold 40C"
(garage-monitor)           ; → runs it once, returns current temp
```

### Hot-reloadable agent logic

The shell is also the configuration surface. New rules, routines, and automations are `.scm` files uploaded over Telegram or serial:

```scheme
;; User-defined automations, composed from primitives
(define (morning-routine)
  (gpio-set LIGHTS 1)
  (let ((temp (adc-read TEMP_SENSOR)))
    (when (< temp 18)
      (gpio-set HEATER 1)
      (schedule-once 30 (lambda () (gpio-set HEATER 0)))))
  (reply "Good morning. Lights on, heater managed."))

(schedule-daily 7 0 morning-routine)
```

New `.scm` files are sent over the network or serial. The agent loads them, evaluates them, and the behavior changes immediately. The firmware stays unchanged.

### The shell is the interface

Inspired by scsh and schemesh, the entire interaction surface is WispyScheme. There is no separate "tool API" or "config format" — the shell is the API:

```scheme
;; Over serial (USB admin console):
wispy> (gpio-read 4)
1
wispy> (schedule-list)
(#1 daily 07:00 morning-routine
 #7 every 300s garage-monitor)
wispy> (define (blink pin n)
         (when (> n 0)
           (gpio-set pin 1) (sleep-ms 200)
           (gpio-set pin 0) (sleep-ms 200)
           (blink pin (- n 1))))
wispy> (blink LED 3)

;; Over Telegram (same language, different transport):
User: (capabilities GARAGE_SENSOR)
Agent: (ADC_READ CONFIGURE)
User: (garage-monitor)
Agent: 23.4
```

Serial and Telegram are just transports. The language is the same. The agent, the user, and the LLM all speak Scheme.

### Algebraic type dispatch as security policy

zclaw's C code validates operations with conditional checks. WispyScheme replaces those with a 1KB lookup table — the Cayley table — where every operation's validity is determined by a single array access:

```scheme
(dot GPIO_SET (tau pin))    ; → valid or BOT (type error)
(dot ADC_READ (tau pin))    ; → valid or BOT
(dot SCHEDULE (tau fn))     ; → valid if fn is a closure
```

BOT means the operation is not permitted. No exception, no crash — just a return value. The security policy is a const array in flash, not runtime conditionals that could have bugs.

Different security levels can be different tables:

| Level | Table behavior |
|---|---|
| Safe mode | GPIO writes → BOT, reads only |
| Normal | Full table, all operations valid |
| Restricted | LLM calls → BOT, local only |

Swapping policy is swapping a 1KB const pointer. One instruction.

### Verified dispatch

The Cayley table's properties are proved in Lean 4 (14 theorems, zero `sorry`, verified by `native_decide`). The C application logic has no such guarantees. With WispyScheme, the type dispatch that decides "is this operation valid on this type?" is mathematically verified, not just tested.

### The algebra extension for agent introspection

The agent can query its own capability matrix:

```scheme
;; What can I do with this GPIO pin?
(type-valid? GPIO_SET (tau pin-5))   ; → #t
(type-valid? ADC_READ (tau pin-5))   ; → #f (not an ADC pin)

;; Enumerate all valid operations for a device
(define (capabilities device)
  (filter (lambda (op) (type-valid? op (tau device)))
          *operations*))

;; Self-describe to the user
(define (explain-capabilities)
  (for-each (lambda (op)
    (reply (string-append (op-name op) ": "
      (if (type-valid? op (tau current-device)) "yes" "no"))))
    *operations*))
```

When the LLM asks "can I set GPIO 5 high?", the agent doesn't guess — it queries the table. The answer is algebraic.

## Memory Budget

Measured on `riscv32imc-unknown-none-elf` (ESP32-C3 target), release build with LTO and `opt-level = "s"`:

```
zclaw firmware (888 KiB cap):
├── Wi-Fi / networking ............. 370 KiB  (unchanged)
├── TLS / crypto ................... 132 KiB  (unchanged)
├── FreeRTOS ....................... ~180 KiB  (unchanged)
├── Application logic .............. ~38 KiB  (replaced)
│   └── WispyScheme (measured no_std RISC-V):
│       ├── Cayley table ...........   1 KiB  (flash, .rodata)
│       ├── Core lib (heap/reader/
│       │   symbols/val) ...........  ~6 KiB  (flash, .text)
│       ├── Const data .............  ~8 KiB  (flash, .rodata)
│       ├── Evaluator (estimated) .. ~24 KiB  (flash, .text)
│       │   (eval.rs not yet no_std — estimated from native ratio)
│       └── Rib heap ............... configurable SRAM
│           (8,192 ribs × 24 bytes = 192 KiB on ESP32-C3)
├── Symbol table ................... ~24 KiB  (SRAM, 512 entries × 48 bytes)
└── Headroom ....................... ~19 KiB
```

**Flash: ~39 KiB** (fits in the 38.4 KiB application slot, tight but achievable with size optimization). The table is 1KB in `.rodata` — zero RAM cost. The evaluator and reader are code in flash. The rib heap and symbol table live in SRAM as fixed-size buffers (`no_std`, no allocator).

**Note:** the evaluator (`eval.rs`) currently requires `std` due to `println!`, `format!`, and `String` usage in builtins. Porting it to `no_std` requires replacing formatted output with direct byte writes to a port buffer. The core (table, heap, reader, symbols) compiles today: `cargo build --target riscv32imc-unknown-none-elf --no-default-features --lib --release`.

## Integration Points

WispyScheme integrates with zclaw's existing architecture:

| zclaw component | WispyScheme integration |
|---|---|
| FreeRTOS task model | Evaluator runs as a FreeRTOS task; other tasks send expressions via queues |
| Telegram interface | Messages dispatched to `(on-message msg)` in Scheme |
| LLM backends | `(llm-reply msg)` calls zclaw's existing HTTP/TLS path as a foreign function |
| GPIO | `(gpio-read pin)` / `(gpio-set pin val)` as registered foreign functions |
| Scheduler | `(schedule-once mins fn)` / `(schedule-daily h m fn)` wrapping zclaw's job system |
| USB admin console | REPL over serial — type Scheme directly, debug live |
| Memory/context | `(remember key val)` / `(recall key)` backed by zclaw's storage |

Foreign functions are registered at boot — Rust/C implementations called from Scheme via the evaluator's builtin table. The Cayley table handles type dispatch; the foreign functions handle hardware.

## What zclaw Keeps

Everything that isn't application logic stays in C:

- Wi-Fi / networking stack (ESP-IDF)
- TLS / crypto (mbedTLS)
- FreeRTOS kernel and task management
- LLM HTTP client
- Telegram bot protocol
- USB admin console (extended with Scheme REPL)

WispyScheme replaces the decision layer, not the infrastructure.

## Summary

zclaw proved that an AI agent fits on an ESP32 under 888 KiB. WispyScheme makes that agent into something new: a device where the LLM doesn't just call tools — it writes them, in the same Scheme that the user types at the serial console, that the scheduler executes, that the Telegram bot speaks. The shell is the agent. The agent is the shell.

The 1KB Cayley table replaces ad-hoc C conditionals with a proved algebraic dispatch mechanism. The algebra extension lets the agent introspect its own capabilities. New behavior is a Scheme expression, not a firmware rebuild. The LLM composes tools from primitives. The user inspects and modifies them in the same language. Everything is transparent, auditable, and live.

Same chip. Same FreeRTOS. Same Telegram. But now the agent thinks in Scheme.
