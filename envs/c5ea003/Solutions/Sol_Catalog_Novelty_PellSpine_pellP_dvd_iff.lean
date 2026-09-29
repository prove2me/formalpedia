-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellP_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:57:50.216069+00:00
-- url     : https://prove2.me/submissions/e3aae95e-4091-4bc5-9af0-c8c13eb2d97a

-- Sol generated from Novelty/PellSpineDivisibility.lean
import Mathlib
import Definitions.Def_Novelty_PellSpineCore
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_gcd
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_injective
/-
# Strong divisibility on the Pell spine — and four conjectures it kills

Building on `Novelty.PellSpineCore`, this file proves that the Pell numbers form a
**strong divisibility sequence**,

`gcd (P m) (P n) = P (gcd m n)`,

and then uses that theorem as a *falsification engine*: four natural strengthenings of
it are each destroyed by a single explicit counterexample, all of them living inside the
first eight Pell numbers.

## Proved

* `pellP_gcd_step`   — the Euclidean step `gcd (P (m+n)) (P n) = gcd (P m) (P n)`;
* `pellP_gcd`        — **strong divisibility** `gcd (P m) (P n) = P (gcd m n)`;
* `pellP_dvd_iff`    — `m ∣ n ↔ P m ∣ P n`, with no side condition at all;
* `pellP_prime_index`— if `P n` is prime then `n` is prime;
* `pellQ_dvd_odd_multiple` — the *guarded* companion statement `Q n ∣ Q ((2k+1) * n)`.

## Refuted (each by one counterexample)

* `not_pellP_prime_of_prime_index`  — `n` prime does **not** force `P n` prime: `P 7 = 169 = 13²`;
* `not_pellP_squarefree`            — Pell numbers are **not** all squarefree: again `P 7 = 13²`
  (the exact analogue for Fibonacci numbers is a well-known open problem, and here it is
  false at the seventh term);
* `not_pellQ_strong_divisibility`   — the companion sequence is **not** a strong divisibility
  sequence: `gcd (Q 3) (Q 6) = gcd 7 99 = 1 ≠ 7 = Q 3`, even though `3 ∣ 6`;
* `not_prime_dvd_pellP_pred`        — the naive Fermat-style law `p ∣ P (p-1)` fails: `3 ∤ P 2 = 2`
  (the correct exponent is `p - (2/p)`, and `2` is a non-residue mod `3`).

The moral, extracted in `FUTURE_DIRECTIONS.md`: strong divisibility is a property of the
*norm-form solution* sequence `P`, not of the *trace* sequence `Q`, and it degrades to a
`2k+1`-graded statement on `Q`.
-/

open Catalog.Novelty.PellSpine

/-! ## The Euclidean step -/



/-! ## Strong divisibility -/




/-! ## The guarded companion statement -/



/-! ## Numerical anchors for the counterexamples -/


/-! ## Four refutations -/








open Catalog.Novelty.PellSpine in
theorem solution(m n : ℕ) : m ∣ n ↔ pellP m ∣ pellP n := by
  constructor
  · intro h
    have : Nat.gcd (pellP m) (pellP n) = pellP m := by
      rw [pellP_gcd, Nat.gcd_eq_left_iff_dvd.mpr h]
    exact Nat.gcd_eq_left_iff_dvd.mp this
  · intro h
    have h1 : Nat.gcd (pellP m) (pellP n) = pellP m := Nat.gcd_eq_left_iff_dvd.mpr h
    rw [pellP_gcd] at h1
    have : Nat.gcd m n = m := pellP_injective h1
    exact Nat.gcd_eq_left_iff_dvd.mp this
