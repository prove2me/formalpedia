-- Prove2me | Theorems.Thm_norm_fourth_power_le_of_tendsto_polynomial_companions
-- name    : norm_fourth_power_le_of_tendsto_polynomial_companions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:48:45.160639+00:00
-- url     : https://prove2.me/theorems/01c45d1d-a715-5e9d-aa38-ba7337c1d6e0
-- title:
--   norm fourth power le of tendsto polynomial companions: norm fourth power le of tendsto polynomial companions
-- statement:
--   The published fourth-power estimate for an operator companion obtained as
--   the operator-norm limit of uniformly sup-norm-bounded polynomial companions.
--   This packages the limiting step needed after a norm-preserving polynomial
--   approximation theorem for the scalar Cauchy companion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L349-L366
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L349-L366

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem norm_fourth_power_le_of_tendsto_polynomial_companions
    (A : E →L[ℂ] E) {K m : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p : Polynomial ℂ) (hp : polynomialSupNorm p S ≤ m)
    (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ)
    (hq : ∀ n, polynomialSupNorm (q n) S ≤ m)
    (hlim : Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
      (nhds G))
    (hsymm : ‖Polynomial.aeval A p + star G‖ ≤ 2 * m) :
    ‖Polynomial.aeval A p‖ ^ 4 ≤
      (2 * K ^ 3 + K ^ 2) * m ^ 4 := by sorry
