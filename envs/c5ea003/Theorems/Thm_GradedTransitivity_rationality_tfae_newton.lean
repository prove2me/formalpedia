-- Prove2me | Theorems.Thm_GradedTransitivity_rationality_tfae_newton
-- name    : GradedTransitivity.rationality_tfae_newton
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:39:40.206394+00:00
-- url     : https://prove2.me/theorems/a9578dff-7ef5-4b3a-ac2c-19c19c07aeb4
-- title:
--   Three-way classification.
-- statement:
--   **Three-way classification.**  For a sequence `a : â â â` and `k : â` the
--   following are equivalent: the denominator `(1-q)^k` clears the generating
--   function; the `k`-th forward difference vanishes eventually; and `a` is
--   eventually a `â`-combination of the `k` shifted binomials `C(Â·-N, j)`.
--
--   ```lean
--   theorem GradedTransitivity.rationality_tfae_newton(k : ℕ) (a : ℕ → ℚ) :
--       ((∃ P : ℚ[X], (1 - PowerSeries.X) ^ k * gen a = (P : PowerSeries ℚ)) ↔
--           EventuallyZero (sdiff^[k] a)) ∧
--         (EventuallyZero (sdiff^[k] a) ↔
--           ∃ (N : ℕ) (d : ℕ → ℚ), ∀ n ≥ N, a n = ∑ j ∈ Finset.range k, d j * binomShift N j n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/Newton.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/Newton.lean#L200

-- Thm stub generated from Shared/GradedTransitivity/Newton.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_Newton
import Definitions.Def_Shared_GradedTransitivity_Structure

/-!
# Newton's forward-difference classification

This file closes the circle around the rationality criterion by proving the
missing *converse*: a sequence whose `k`-th forward difference vanishes
eventually is, from that point on, a `ℚ`-linear combination of the `k`
binomial functions `n ↦ C(n-N, j)`, `j < k` (Newton's forward difference
formula).  Together with `FiniteDifference` this yields the classification

`(1-q)^k` clears `∑ a n qⁿ`
  ⟺ `Δ^k a` vanishes eventually
  ⟺ `a` is eventually a combination of `C(·-N, j)`, `j < k`.

For a graded `G`-set this says: eventual `r`-transitivity is only the simplest
member of a hierarchy, and the exponent `k` in the denominator measures exactly
the binomial degree of the orbit-counting sequence.

## Main results

* `newton_forward` : Newton's forward difference formula.
* `sdiff_iter_binom_eq_zero` : the binomial functions are annihilated.
* `rationality_tfae_newton` : the three-way classification.
-/

open GradedTransitivity

open Polynomial

/-! ### Linearity of the difference operator -/




/-! ### The shifted binomial functions -/





/-! ### Newton's forward difference formula -/





/-! ### The classification -/

theorem GradedTransitivity.rationality_tfae_newton(k : ℕ) (a : ℕ → ℚ) :
    ((∃ P : ℚ[X], (1 - PowerSeries.X) ^ k * gen a = (P : PowerSeries ℚ)) ↔
        EventuallyZero (sdiff^[k] a)) ∧
      (EventuallyZero (sdiff^[k] a) ↔
        ∃ (N : ℕ) (d : ℕ → ℚ), ∀ n ≥ N, a n = ∑ j ∈ Finset.range k, d j * binomShift N j n) := by sorry
