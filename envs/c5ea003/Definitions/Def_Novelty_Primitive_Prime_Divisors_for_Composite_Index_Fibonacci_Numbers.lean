-- Prove2me | Definitions.Def_Novelty_Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers
-- name    : Novelty_Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:36:45.298877+00:00
-- url     : https://prove2.me/theorems/656c674f-7d8d-4650-9e9b-60fb4ed175fd
-- title:
--   Aether Catalog definitions — Novelty_Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Primitive.Prime.Divisors.for.Composite.Index.Fibonacci.Numbers`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers.lean by skeleton subtraction
import Mathlib

/-!
# Primitive prime divisors for composite-index Fibonacci numbers

## Provenance

The file that previously occupied this slot in the catalog was not a Lean file at
all: it was a stray fragment of a *unified diff* against a module that does not
exist in the project.  It is preserved verbatim in the comment block below so that
no user-supplied content is lost.  Its mathematical content was a single
unfinished statement, `wall_base`, asserting that

  `v_p (F(np) / F(n)) = 1`  for an odd prime `p` with `p ∣ F(n)`,

together with a proof sketch.  That statement (a form of the "Wall base case" in
the theory of the Fibonacci `p`-adic valuation) is *not* proved here: it depends on
a lifting-the-exponent computation modulo `p²` for which the catalog has no
supporting API.  Instead, this file develops, with complete proofs, the part of the
primitive-divisor theory that the `wall_base` lemma was meant to feed into: the
*rank of apparition* and its interaction with composite indices.

Original fragment (not valid Lean, retained for reference):

```
--- a/Speculative/AutoResearch/Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers.lean
+++ b/Speculative/AutoResearch/Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers.lean
@@ -99,6 +99,9 @@
     (show p ∣ Nat.fib (n + 1) from by rwa [← ZMod.natCast_eq_zero_iff]))
     (by aesop)

+/-- Key helper: F(np)/F(n) ≡ p · F(n+1)^{p-1} (mod p²).
+    Since gcd(F(n+1), p) = 1, Fermat gives F(n+1)^{p-1} ≡ 1 (mod p),
+    so F(np)/F(n) ≡ p (mod p²), hence v_p(F(np)/F(n)) = 1. -/
 -- Wall base case: v_p(F(np)/F(n)) = 1 for odd prime p | F(n)
 lemma wall_base (n p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
     (hpn : p ∣ Nat.fib n) (hn : 2 ≤ n) :
```

## Main results

* `FibPrimitive.exists_pos_dvd_fib` — every `m ≥ 1` divides some positive-index
  Fibonacci number (existence of the rank of apparition), proved by a pigeonhole
  argument on the state pairs `(F k, F (k+1))` in `ZMod m`.
* `FibPrimitive.dvd_fib_iff_fibRank_dvd` — `m ∣ F n ↔ rank(m) ∣ n`.
* `FibPrimitive.isPrimitiveDivisor_iff_fibRank_eq` — `m` is a primitive divisor of
  `F n` exactly when `n` is the rank of apparition of `m`.
* `FibPrimitive.fibRank_fib` — the rank of apparition of `F n` is `n` (for `n ≥ 3`).
* `FibPrimitive.not_isPrimitiveDivisor_of_dvd_proper_divisor` and
  `FibPrimitive.primitive_divisor_composite_coprime` — the composite-index
  obstruction: at a composite index `n = a * b` a primitive divisor must be coprime
  to `F a` and to `F b`.
-/

namespace FibPrimitive

open Nat

/-! ## The state pair sequence modulo `m` -/

/-- The state of the Fibonacci recursion at time `k`, read modulo `m`. -/
private def fibState (m k : ℕ) : ZMod m × ZMod m := ((Nat.fib k : ZMod m), (Nat.fib (k + 1) : ZMod m))




/-! ## The rank of apparition -/

/-- The **rank of apparition** of `m`: the least positive index `n` with `m ∣ F n`
(and `0` if no such index exists, which by `exists_pos_dvd_fib` happens only for
`m = 0`). -/
noncomputable def fibRank (m : ℕ) : ℕ := sInf {n | 0 < n ∧ m ∣ Nat.fib n}






/-! ## Primitive divisors -/

/-- `m` is a **primitive divisor** of `F n` if it divides `F n` but no earlier
Fibonacci number of positive index. -/
def IsPrimitiveDivisor (m n : ℕ) : Prop :=
  m ∣ Nat.fib n ∧ ∀ k, 0 < k → k < n → ¬ m ∣ Nat.fib k



/-! ## The composite-index obstruction -/




end FibPrimitive


