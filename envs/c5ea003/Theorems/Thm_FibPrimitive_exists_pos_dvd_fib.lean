-- Prove2me | Theorems.Thm_FibPrimitive_exists_pos_dvd_fib
-- name    : FibPrimitive.exists_pos_dvd_fib
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:48:50.853794+00:00
-- url     : https://prove2.me/theorems/6e24c01a-5fb6-42da-87fe-f8bcf0d112c7
-- title:
--   Existence of the rank of apparition.
-- statement:
--   **Existence of the rank of apparition.** Every positive `m` divides a Fibonacci
--   number of positive index.  The proof is a pigeonhole argument: the state map
--   `k ↦ (F k, F (k+1))` from `ℕ` to the finite set `ZMod m × ZMod m` cannot be
--   injective, and the recursion can be run backwards, so the coincidence propagates
--   down to index `0`, where `F 0 = 0`.
--
--   ```lean
--   theorem FibPrimitive.exists_pos_dvd_fib(m : ℕ) (hm : 0 < m) : ∃ n, 0 < n ∧ m ∣ Nat.fib n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers.lean#L91

-- Thm stub generated from Novelty/Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers.lean
import Mathlib
import Definitions.Def_Novelty_Primitive_Prime_Divisors_for_Composite_Index_Fibonacci_Numbers

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

open FibPrimitive

open Nat

/-! ## The state pair sequence modulo `m` -/

theorem FibPrimitive.exists_pos_dvd_fib(m : ℕ) (hm : 0 < m) : ∃ n, 0 < n ∧ m ∣ Nat.fib n := by sorry
