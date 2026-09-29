-- Prove2me | Theorems.Thm_HalfPlane_card_fiber
-- name    : HalfPlane.card_fiber
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:22:34.138981+00:00
-- url     : https://prove2.me/theorems/9c26dcf9-fe88-4c49-8843-95625ee2dfd0
-- title:
--   Each circle point modulo `M` has exactly `p` lifts modulo `pM`.
-- statement:
--   **Each circle point modulo `M` has exactly `p` lifts modulo `pM`.**
--
--   ```lean
--   theorem HalfPlane.card_fiber(p M a b : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hM : 2 ≤ M)
--       (hpM : p ∣ M) (ha : a < M) (hb : b < M) (hcirc : (a ^ 2 + b ^ 2) % M = 1 % M) :
--       ((circleFinset (p * M)).filter (fun q => (q.1 % M, q.2 % M) = (a, b))).card = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlanePrimePower.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlanePrimePower.lean#L159

-- Thm stub generated from MachineLearning/HalfPlanePrimePower.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneClosedForm

/-!
# Cycle 5: Hensel lifting for the modular circle

The conic `x² + y² = 1` is smooth over `F_p` for odd `p` (its gradient `(2x, 2y)`
never vanishes on the curve), so every solution modulo `M` lifts to exactly `p`
solutions modulo `pM` whenever `p ∣ M`.  Formally:

* `card_lift_solutions` : a non-degenerate linear congruence in two unknowns over
  `F_p` has exactly `p` solutions;
* `circleCount_mul_of_prime_dvd` : `C(pM) = p·C(M)` for `p` an odd prime dividing `M`;
* `circleCount_prime_pow` : `C(p^k) = p^{k-1}(p - χ_p(-1))`;
* `circleCount_odd` : the completely explicit formula
  `C(N) = ∏_{p ∣ N} p^{v_p(N)-1}(p - χ_p(-1))` for every odd `N ≥ 1`.

This closes the separable baseline: `C` is a closed-form function of the
factorisation of `N`, in stark contrast with the half-plane count `H`, which is not
multiplicative at all.
-/

open HalfPlane

open Finset

/-! ### Counting the lifts -/



/-! ### The lifting criterion -/





/-! ### The lifting bijection -/

theorem HalfPlane.card_fiber(p M a b : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hM : 2 ≤ M)
    (hpM : p ∣ M) (ha : a < M) (hb : b < M) (hcirc : (a ^ 2 + b ^ 2) % M = 1 % M) :
    ((circleFinset (p * M)).filter (fun q => (q.1 % M, q.2 % M) = (a, b))).card = p := by sorry
