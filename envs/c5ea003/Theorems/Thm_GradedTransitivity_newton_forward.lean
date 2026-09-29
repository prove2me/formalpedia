-- Prove2me | Theorems.Thm_GradedTransitivity_newton_forward
-- name    : GradedTransitivity.newton_forward
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:38:53.64393+00:00
-- url     : https://prove2.me/theorems/6c84c708-4b92-4803-9a10-5206a1726ad3
-- title:
--   Newton's forward difference formula.
-- statement:
--   **Newton's forward difference formula.**  If `Î^k a` vanishes from `N` on,
--   then from `N` on, `a` is the explicit binomial combination
--   `a n = â_{j<k} (Î^j a)(N) Â· C(n-N, j)`.
--
--   ```lean
--   theorem GradedTransitivity.newton_forward{k N : ℕ} {a : ℕ → ℚ} (h : ∀ n ≥ N, sdiff^[k] a n = 0) :
--       ∀ n ≥ N, a n = ∑ j ∈ Finset.range k, (sdiff^[j] a N) * (((n - N).choose j : ℚ)) := by sorry
--   /-! ### The classification -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/Newton.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/Newton.lean#L180

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

theorem GradedTransitivity.newton_forward{k N : ℕ} {a : ℕ → ℚ} (h : ∀ n ≥ N, sdiff^[k] a n = 0) :
    ∀ n ≥ N, a n = ∑ j ∈ Finset.range k, (sdiff^[j] a N) * (((n - N).choose j : ℚ)) := by sorry
