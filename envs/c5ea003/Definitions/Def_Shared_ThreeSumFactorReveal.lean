-- Prove2me | Definitions.Def_Shared_ThreeSumFactorReveal
-- name    : Shared_ThreeSumFactorReveal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:49:08.196269+00:00
-- url     : https://prove2.me/theorems/8a1b9075-021d-4868-8701-559071de3c87
-- title:
--   Aether Catalog definitions — Shared_ThreeSumFactorReveal
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ThreeSumFactorReveal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ThreeSumFactorReveal.lean by skeleton subtraction
import Mathlib

set_option maxRecDepth 40000

/-!
# 3SUM modulo a prime factor reveals that factor

Let `N = p * q` be a semiprime.  Any natural number `s` with

* `0 < s < N`, and
* `p ∣ s`

satisfies `Nat.gcd s N = p`: the gcd *reveals* the factor `p`, and no side
condition `¬ q ∣ s` is needed — it is automatic, because `q ∣ s` together with
`p ∣ s` would force `N ∣ s`, contradicting `s < N`.

Applied to `s = a + b + c` this is the *3SUM mod-p factor reveal*: a triple whose
sum vanishes modulo `p` but whose integer sum is a nonzero number below `N`
produces `p` by one gcd computation.  The same argument is given for `r`-sums
(sums over an arbitrary `Finset`) and for *collisions*, where the revealing
quantity is a difference of two sums.

The final section contains machine-checked counts for `N = 143 = 11 * 13`
(Lab Notes).

Main results:

* `gcd_eq_prime_of_dvd_of_lt` — the reveal lemma.
* `threeSum_gcd_reveal` — 3SUM form.
* `sumFinset_gcd_reveal` — general `r`-sum form.
* `collision_gcd_reveal` — collision (difference of two sums) form.
* `threeSum_reveal_or_equal` — dichotomy for a modular collision of two triples.
-/

namespace ThreeSumReveal

/-! ## The reveal lemma -/







/-! ## No triple below `N` can be divisible by both factors

This is the structural reason the "mod-both" column of the experiment is empty. -/


/-! ## Lab Notes: `N = 143 = 11 * 13`

Machine-checked counts over all triples `1 ≤ a < b < c ≤ 12`:

* `19`-style census: `20` triples have `11 ∣ a + b + c` and `13 ∤ a + b + c`;
* `0` triples have both `11 ∣ a + b + c` and `13 ∣ a + b + c`
  (forced by `not_dvd_both_of_lt`, since every such sum is `< 143`).

(The count `20` is for the range `1 ≤ a < b < c ≤ 12`; for `1 ≤ a < b < c ≤ 11`
the count is `15`.  The exact range is what fixes the number.) -/

/-- Ordered triples `1 ≤ a < b < c ≤ n`, as a `Finset`. -/
def triples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n)).filter
    (fun x => x.1 < x.2.1 ∧ x.2.1 < x.2.2)

/-- Sum of a triple. -/
def tsum (x : ℕ × ℕ × ℕ) : ℕ := x.1 + x.2.1 + x.2.2





end ThreeSumReveal


