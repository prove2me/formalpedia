-- Prove2me | Theorems.Thm_norm_triple_le_of_tendsto_polynomial_companions
-- name    : norm_triple_le_of_tendsto_polynomial_companions
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:48:56.311073+00:00
-- url     : https://prove2.me/theorems/58d075dc-7b2a-4b98-a54c-915a8dab1b0f
-- title:
--   norm triple le of tendsto polynomial companions: norm triple le of tendsto polynomial companions
-- statement:
--   Polynomial companion estimates pass to an operator-norm limit.  If
--   `q n (A) → G` and every `q n` has sup norm at most `m`, then the global
--   polynomial-calculus bound controls `p(A) G p(A)` by `K m³`.
--
--   This statement isolates the exact approximation interface required for a
--   holomorphic Cauchy companion: construction of the approximants and their
--   uniform scalar bound are analytic inputs, while the limiting operator
--   estimate is purely functional-analytic.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L316-L343
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L316-L343

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem norm_triple_le_of_tendsto_polynomial_companions
    (A : E →L[ℂ] E) {K m : ℝ} (hK : 0 ≤ K)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p : Polynomial ℂ) (hp : polynomialSupNorm p S ≤ m)
    (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ)
    (hq : ∀ n, polynomialSupNorm (q n) S ≤ m)
    (hlim : Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
      (nhds G)) :
    ‖Polynomial.aeval A p * G * Polynomial.aeval A p‖ ≤ K * m ^ 3 := by sorry
