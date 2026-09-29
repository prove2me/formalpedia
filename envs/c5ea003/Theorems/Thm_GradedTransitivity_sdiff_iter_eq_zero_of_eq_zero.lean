-- Prove2me | Theorems.Thm_GradedTransitivity_sdiff_iter_eq_zero_of_eq_zero
-- name    : GradedTransitivity.sdiff_iter_eq_zero_of_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:39:50.301076+00:00
-- url     : https://prove2.me/theorems/4d79096a-c425-4350-89b9-0f7c76f96029
-- title:
--   Iterated differences of a sequence that vanishes from `N` on still vanish
-- statement:
--   Iterated differences of a sequence that vanishes from `N` on still vanish
--   from `N` on.
--
--   ```lean
--   theorem GradedTransitivity.sdiff_iter_eq_zero_of_eq_zero{f : ℕ → ℚ} {N : ℕ} (h : ∀ n ≥ N, f n = 0) (k : ℕ) :
--       ∀ n ≥ N, sdiff^[k] f n = 0 := by sorry
--   /-! ### The shifted binomial functions -/
--
--
--
--
--
--   /-! ### Newton's forward difference formula -/
--
--
--
--
--
--   /-! ### The classification -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/Newton.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/Newton.lean#L59

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

theorem GradedTransitivity.sdiff_iter_eq_zero_of_eq_zero{f : ℕ → ℚ} {N : ℕ} (h : ∀ n ≥ N, f n = 0) (k : ℕ) :
    ∀ n ≥ N, sdiff^[k] f n = 0 := by sorry
