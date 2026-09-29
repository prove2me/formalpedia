-- Prove2me | Theorems.Thm_ThreeSumReveal_collision_gcd_reveal
-- name    : ThreeSumReveal.collision_gcd_reveal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:53:07.236241+00:00
-- url     : https://prove2.me/theorems/ab2d1b77-64e6-445c-be7f-33c80ce54ef5
-- title:
--   Collision form.
-- statement:
--   **Collision form.**  A *collision* `s â¡ t (mod p)` between two integer
--   quantities `t < s < N` reveals `p` through `gcd (s - t) N`.  This is the shape
--   produced by sumset (`a + b â¡ c + d`) and by 3SUM (`a + b + c â¡ d + e + f`)
--   searches.
--
--   ```lean
--   theorem ThreeSumReveal.collision_gcd_reveal{p q s t : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hts : t < s) (hlt : s < p * q) (hdvd : p ∣ s - t) :
--       Nat.gcd (s - t) (p * q) = p := by sorry
--
--
--   /-! ## No triple below `N` can be divisible by both factors
--
--   This is the structural reason the "mod-both" column of the experiment is empty. -/
--
--
--   /-! ## Lab Notes: `N = 143 = 11 * 13`
--
--   Machine-checked counts over all triples `1 ≤ a < b < c ≤ 12`:
--
--   * `19`-style census: `20` triples have `11 ∣ a + b + c` and `13 ∤ a + b + c`;
--   * `0` triples have both `11 ∣ a + b + c` and `13 ∣ a + b + c`
--     (forced by `not_dvd_both_of_lt`, since every such sum is `< 143`).
--
--   (The count `20` is for the range `1 ≤ a < b < c ≤ 12`; for `1 ≤ a < b < c ≤ 11`
--   the count is `15`.  The exact range is what fixes the number.) -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ThreeSumFactorReveal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ThreeSumFactorReveal.lean#L76

-- Thm stub generated from Shared/ThreeSumFactorReveal.lean
import Mathlib
import Definitions.Def_Shared_ThreeSumFactorReveal

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

open ThreeSumReveal

/-! ## The reveal lemma -/

theorem ThreeSumReveal.collision_gcd_reveal{p q s t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hts : t < s) (hlt : s < p * q) (hdvd : p ∣ s - t) :
    Nat.gcd (s - t) (p * q) = p := by sorry
