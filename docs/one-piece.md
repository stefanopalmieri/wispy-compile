# One Piece

A computer you can own and trust, from the axioms to the silicon.

## The Insight

Type dispatch in every language runtime is a program — conditionals, vtables, match arms, method resolution. Programs have bugs. Programs are opaque. Programs are maintained by someone else.

Type dispatch can be a mathematical object instead. A 32x32 Cayley table. 1KB. Constant. Verified by Z3 and Lean. It doesn't execute — it *is*. The same table is the runtime, the type system, the error model, and the API.

This single insight cascades into everything below.

## The Algebra

The 12-element algebraic core encodes three independent capabilities, proved in Lean with zero `sorry`:

- **Self-representation.** Q and E are mutual inverses on the core. Code becomes data, data becomes code, round-trip guaranteed by axioms. This is homoiconicity with a proof.
- **Self-description.** TAU classifies any value by type in one lookup. The language can answer "what am I looking at?" without branching.
- **Self-execution.** RHO dispatches on the classifier. Y provides the algebraic fixed point. Together: conditional recursion, the minimal engine of computation.

The remaining 20 elements extend the core with R4RS type tags and special values. The full table has 14 Lean-verified theorems: absorbers, retraction, classifier dichotomy, branch, composition, fixed point, extensionality, type dispatch. All proved computationally via `native_decide` in 6 seconds.

## The Language

WispyScheme is an R4RS Scheme built on the table. 104 builtins, three execution backends (interpreter, CPS evaluator, compiler), under 5,000 lines of Rust. It passes R4RS programs unchanged. The algebra is invisible unless you reach for it.

When you reach for it:

```scheme
(dot CAR T_PAIR)          ; → T_PAIR (the table says: valid)
(dot CAR T_STR)           ; → BOT (the table says: type error)
(tau (cons 1 2))          ; → T_PAIR (the table says: it's a pair)
(type-valid? CAR T_PAIR)  ; → #t
```

Three primitives — `dot`, `tau`, `type-valid?` — expose the entire dispatch mechanism. The programmer works with the same algebraic elements the evaluator uses. The boundary between language and implementation dissolves. This is the only language where the runtime is also the API.

## The Verification Chain

Every layer is proved or provable:

| Layer | Proved by | Property |
|---|---|---|
| Algebra | Lean (`native_decide`) | 14 theorems, zero `sorry` |
| Kernel | Isabelle/HOL (seL4) | Functional correctness, isolation |
| ISA | RISC-V formal spec | Instruction semantics |
| Toolchain | Open source (Yosys + nextpnr) | Auditable synthesis |

No trust required at any layer. No proprietary blobs. No "it works because we tested it." The algebra is correct because the axioms require it. The kernel is correct because the proof says so. The hardware is correct because the spec is formal and the tools are open.

## The Hardware

The Cayley table is 1KB. It fits in flash on any microcontroller. But it can also be a ROM in a processor's execute stage — a custom RISC-V instruction:

```
DOT rd, rs1, rs2    # rd = CAYLEY[rs1][rs2], one cycle
```

A 10-bit address, 5-bit output ROM. Smaller than a multiply unit. On a VexRiscv softcore (SpinalHDL plugin, ~80 lines), synthesized on a $70 Lattice ECP5 FPGA with a fully open toolchain. Type dispatch becomes a single-cycle hardware operation — the same status as `ADD`.

The 64-element version (4KB ROM) adds immediate fixnum arithmetic and built-in symbol recognition. Small integer math as a table lookup. In hardware. One cycle.

This is what Lisp machines were trying to be. Symbolics spent $100 million and a decade. This is a 1KB ROM on a $70 FPGA, proved correct by Lean, running a verified microkernel.

## The Stack

```
Wisp syntax over serial / MQTT / HTTP
        │
WispyScheme (R4RS + algebra extension)
  Evaluator: 104 builtins + FFI to Rust/C
  Cayley table: 1KB, proved correct (Lean)
        │
seL4 microkernel
  Capability-based isolation, proved correct (Isabelle/HOL)
  Rust userspace via sel4-microkit
        │
VexRiscv on Lattice ECP5
  RV32IMA + Sv32 MMU + DOT custom instruction
  Open source: Yosys + nextpnr, no proprietary tools
        │
$70 FPGA board (ULX3S / OrangeCrab)
  UART, SPI, I2C, GPIO, WiFi
```

Every layer is open. Every critical layer is verified. The entire system fits on a board you can hold in your hand.

## The Shell

Wisp syntax (SRFI-119) replaces parentheses with indentation:

```
define : read-temp sensor
  let : : raw : adc-read sensor
    if : > raw 512
      begin
        led-on
        alarm raw
      led-off
```

On a serial console, every parenthesis is a keystroke wisp eliminates. The reader desugars indentation into S-expressions; everything downstream is oblivious. Full parenthesized Scheme is always accepted. Two syntaxes, one language.

On a workstation, brace/paren switching (inspired by schemesh) gives you shell and Scheme in the same session:

```scheme
{ls -la | grep ".rs$"}                    ;; shell
(for-each display (sh-run/lines {find . -name "*.scm"}))  ;; Scheme
```

The scsh lineage (1994) proved Scheme could be a shell. Schemesh (2024) proved it could be a good one. WispyScheme proves it can run on a $5 chip with algebraic dispatch.

## The Agent

The algebra extension makes WispyScheme a natural agent harness:

- **TAU classifies** — the agent knows what it's looking at
- **DOT dispatches** — the agent's decisions are table lookups, auditable and finite
- **Q/E reify and reflect** — the agent can represent its own actions as data and execute data as actions
- **BOT propagates** — invalid operations return BOT instead of throwing, so type dispatch is data flow

A finite algebra with 32 elements can't express an operation the table doesn't contain. The decision space is enumerable. An agent running on this algebra can be audited exhaustively — not by reading logs, but by querying the table.

On a ZeroClaw edge node: SOPs are Scheme scripts uploaded over MQTT. The Cayley table is the security policy — swap the table, swap the autonomy level. seL4 capabilities isolate the evaluator from the drivers. The agent can query its own capability matrix with `(dot op tag)`.

## The Security Model

Three layers, all verified, all static:

| Layer | Mechanism | Enforces |
|---|---|---|
| Language | Cayley table | "Can `car` operate on a string?" |
| Kernel | seL4 capabilities | "Can this task access UART?" |
| Hardware | MMU | "Can this address be read?" |

Switching security policy is swapping a 1KB const array and an seL4 capability set. No runtime flags. No checks that could be bypassed. The algebra says no. The kernel says no. The hardware says no.

## The Economics

| Component | Cost |
|---|---|
| ECP5 FPGA board | ~$70 |
| VexRiscv softcore | Free (open source) |
| seL4 microkernel | Free (open source, GPL) |
| WispyScheme | Free (MIT) |
| Yosys + nextpnr | Free (open source) |
| Lean 4 | Free (open source) |

A verified autonomous computing platform for under $100. No vendor lock-in. No license fees. No proprietary tools anywhere in the chain.

For production deployment on fixed silicon (SiFive U74 or similar), the `DOT` instruction lives in L1 cache instead of a ROM — still fast, still correct, still verified. The FPGA is the development platform; ASIC is the endgame.

## What This Is

A computer where:

- The language runtime is a 1KB mathematical object, not a program
- The programmer can see and query the dispatch mechanism with three primitives
- The OS kernel is proved correct, not just tested
- The hardware is open source, auditable, and modifiable
- Every layer of the verification chain is machine-checked
- New behavior is uploaded as Scheme scripts, not firmware reflashes
- The whole thing costs less than lunch

This is what computing was supposed to be. A machine that does what you say and nothing else, because every layer — from the axioms to the silicon — is proved, open, and yours.

Named after a guinea pig.
