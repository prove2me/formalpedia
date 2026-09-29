-- Prove2me | Theorems.Thm_HalfPlane_card_lift_solutions
-- name    : HalfPlane.card_lift_solutions
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T15:22:19.459061+00:00
-- url     : https://prove2.me/theorems/660d8a74-3b76-4df9-8382-2e7be66e10a3
-- title:
--   The lifting condition `c + 2(as + bt) ≡ 0 (mod p)` has exactly `p` solutions
-- statement:
--   The lifting condition `c + 2(as + bt) ≡ 0 (mod p)` has exactly `p` solutions
--   `(s,t) ∈ [0,p)²` as soon as `p` does not divide both `a` and `b`.
--
--   ```lean
--   theorem HalfPlane.card_lift_solutions(p a b c : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
--       (hab : ¬ (p ∣ a ∧ p ∣ b)) :
--       (((Finset.range p) ×ˢ (Finset.range p)).filter
--         (fun st => p ∣ (c + 2 * (a * st.1 + b * st.2)))).card = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlanePrimePower.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlanePrimePower.lean#L62

-- Thm stub generated from MachineLearning/HalfPlanePrimePower.lean
import Mathlib
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

theorem HalfPlane.card_lift_solutions(p a b c : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (hab : ¬ (p ∣ a ∧ p ∣ b)) :
    (((Finset.range p) ×ˢ (Finset.range p)).filter
      (fun st => p ∣ (c + 2 * (a * st.1 + b * st.2)))).card = p := by sorry
