// Benchmark harness for compiled Kamea Scheme nqueens
// Compile: rustc -O -o /tmp/kamea_bench bench.rs
// Run: /tmp/kamea_bench

#![allow(non_snake_case, unused_variables, unused_mut, unused_parens)]

const TOP: u8 = 0;
const T_PAIR: u8 = 12;

#[derive(Clone, Copy, PartialEq, Eq)]
struct Val(i64);

impl Val {
    const NIL: Val = Val(0);
    #[inline(always)]
    const fn fixnum(n: i64) -> Val { Val((n << 1) | 1) }
    #[inline(always)]
    const fn rib(idx: usize) -> Val { Val((idx as i64) << 1) }
    #[inline(always)]
    fn is_fixnum(self) -> bool { (self.0 & 1) != 0 }
    #[inline(always)]
    fn as_fixnum(self) -> Option<i64> {
        if self.is_fixnum() { Some(self.0 >> 1) } else { None }
    }
    #[inline(always)]
    fn as_rib(self) -> usize { (self.0 >> 1) as usize }
}

#[derive(Clone, Copy)]
struct Rib { car: Val, cdr: Val, tag: u8 }

static mut HEAP: Vec<Rib> = Vec::new();
static mut HP: usize = 0;

fn heap_init() {
    unsafe {
        HEAP = Vec::with_capacity(2_000_000);
        HEAP.push(Rib { car: Val::NIL, cdr: Val::NIL, tag: TOP });
        HP = 1;
    }
}

fn heap_reset() {
    unsafe { HP = 1; }
}

#[inline]
fn cons(car: Val, cdr: Val) -> Val {
    unsafe {
        let idx = HP;
        if idx >= HEAP.len() {
            HEAP.push(Rib { car, cdr, tag: T_PAIR });
        } else {
            HEAP[idx] = Rib { car, cdr, tag: T_PAIR };
        }
        HP = idx + 1;
        Val::rib(idx)
    }
}

#[inline(always)]
fn car(v: Val) -> Val {
    if v.is_fixnum() || v == Val::NIL { return Val::NIL; }
    unsafe { HEAP[v.as_rib()].car }
}

#[inline(always)]
fn cdr(v: Val) -> Val {
    if v.is_fixnum() || v == Val::NIL { return Val::NIL; }
    unsafe { HEAP[v.as_rib()].cdr }
}

#[inline(always)]
fn is_true(v: Val) -> bool {
    v != Val::NIL && v.0 != 0
}

#[inline(always)]
fn bool_to_val(b: bool) -> Val {
    if b { Val::fixnum(1) } else { Val::NIL }
}

// ── N-Queens ─────────────────────────────────────────────────────

fn abs_diff(a: Val, b: Val) -> Val {
    let a = a.as_fixnum().unwrap();
    let b = b.as_fixnum().unwrap();
    Val::fixnum(if a > b { a - b } else { b - a })
}

fn safe_p(queen: Val, dist: Val, placed: Val) -> Val {
    if placed == Val::NIL {
        Val::fixnum(1) // true
    } else {
        let q = car(placed);
        if queen.as_fixnum() == q.as_fixnum() {
            Val::NIL // false
        } else if abs_diff(queen, q).as_fixnum() == dist.as_fixnum() {
            Val::NIL // false
        } else {
            safe_p(queen, Val::fixnum(dist.as_fixnum().unwrap() + 1), cdr(placed))
        }
    }
}

fn nqueens_count(n: Val, row: Val, placed: Val) -> Val {
    if row.as_fixnum() == n.as_fixnum() {
        Val::fixnum(1)
    } else {
        count_cols(n, Val::fixnum(0), row, placed)
    }
}

fn count_cols(n: Val, col: Val, row: Val, placed: Val) -> Val {
    if col.as_fixnum() == n.as_fixnum() {
        Val::fixnum(0)
    } else {
        let s = if is_true(safe_p(col, Val::fixnum(1), placed)) {
            nqueens_count(n, Val::fixnum(row.as_fixnum().unwrap() + 1), cons(col, placed))
        } else {
            Val::fixnum(0)
        };
        Val::fixnum(
            s.as_fixnum().unwrap() +
            count_cols(n, Val::fixnum(col.as_fixnum().unwrap() + 1), row, placed).as_fixnum().unwrap()
        )
    }
}

fn nqueens(n: Val) -> Val {
    nqueens_count(n, Val::fixnum(0), Val::NIL)
}

// ── Counter arithmetic ───────────────────────────────────────────

fn fib(n: Val) -> Val {
    let n = n.as_fixnum().unwrap();
    if n < 2 { Val::fixnum(n) }
    else { Val::fixnum(fib(Val::fixnum(n-1)).as_fixnum().unwrap() + fib(Val::fixnum(n-2)).as_fixnum().unwrap()) }
}

fn fib_iter(n: Val) -> Val {
    let n = n.as_fixnum().unwrap();
    let (mut a, mut b) = (0i64, 1i64);
    for _ in 0..n { let t = a + b; a = b; b = t; }
    Val::fixnum(a)
}

fn fact(n: Val) -> Val {
    let n = n.as_fixnum().unwrap();
    if n == 0 { Val::fixnum(1) }
    else { Val::fixnum(n * fact(Val::fixnum(n-1)).as_fixnum().unwrap()) }
}

fn power(base: Val, exp: Val) -> Val {
    let exp = exp.as_fixnum().unwrap();
    if exp == 0 { Val::fixnum(1) }
    else { Val::fixnum(base.as_fixnum().unwrap() * power(base, Val::fixnum(exp-1)).as_fixnum().unwrap()) }
}

fn gcd(a: Val, b: Val) -> Val {
    let b = b.as_fixnum().unwrap();
    if b == 0 { a }
    else { gcd(Val::fixnum(b), Val::fixnum(a.as_fixnum().unwrap() % b)) }
}

fn counter_arith() -> Val {
    Val::fixnum(
        fib(Val::fixnum(8)).as_fixnum().unwrap() +
        fib_iter(Val::fixnum(30)).as_fixnum().unwrap() +
        fact(Val::fixnum(10)).as_fixnum().unwrap() +
        power(Val::fixnum(2), Val::fixnum(10)).as_fixnum().unwrap() +
        gcd(Val::fixnum(100), Val::fixnum(75)).as_fixnum().unwrap()
    )
}

fn main() {
    heap_init();

    // Verify correctness
    assert_eq!(nqueens(Val::fixnum(8)).as_fixnum().unwrap(), 92);
    assert_eq!(counter_arith().as_fixnum().unwrap(), 4461910);

    // Benchmark counter arithmetic
    let iters = 1_000_000;
    let t0 = std::time::Instant::now();
    let mut result = Val::NIL;
    for _ in 0..iters {
        result = counter_arith();
    }
    let elapsed = t0.elapsed();
    let per_iter_us = elapsed.as_secs_f64() / iters as f64 * 1e6;
    println!("Counter arithmetic: {:.3} µs/iter ({} iters, result={})",
             per_iter_us, iters, result.as_fixnum().unwrap());

    // Benchmark N-Queens(8)
    let nq_iters = 10_000;
    let t0 = std::time::Instant::now();
    let mut nq_result = Val::NIL;
    for _ in 0..nq_iters {
        heap_reset();
        nq_result = nqueens(Val::fixnum(8));
    }
    let elapsed = t0.elapsed();
    let per_iter_us = elapsed.as_secs_f64() / nq_iters as f64 * 1e6;
    println!("N-Queens(8):        {:.1} µs/iter ({} iters, result={})",
             per_iter_us, nq_iters, nq_result.as_fixnum().unwrap());
}
