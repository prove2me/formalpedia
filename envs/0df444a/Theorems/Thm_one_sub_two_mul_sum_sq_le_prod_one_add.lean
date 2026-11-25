-- Prove2me | Theorems.Thm_one_sub_two_mul_sum_sq_le_prod_one_add
-- name    : one_sub_two_mul_sum_sq_le_prod_one_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:20:53.242611+00:00
-- url     : https://prove2.me/theorems/a9b2b207-ba98-4c63-9ad1-ca988569cf14
-- title:
--   one sub two mul sum sq le prod one add: one sub two mul sum sq le prod one add
-- statement:
--   **Weierstrass-type product lower bound.** If `∑ aᵢ = 0` and every `|aᵢ| ≤ 1/2`,
--   then `∏ (1 + aᵢ) ≥ 1 - 2 ∑ aᵢ²`.
--
--   Mathematically: a multiplicative perturbation with vanishing first-order term loses
--   volume only to second order. Proof: `∏ (1 + aᵢ) ≥ ∏ exp (aᵢ - 2aᵢ²)
--   = exp (∑ aᵢ - 2 ∑ aᵢ²) = exp (-2 ∑ aᵢ²) ≥ 1 - 2 ∑ aᵢ²`, using
--   `Real.exp_sub_two_mul_sq_le` and `Real.add_one_le_exp`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/JohnIngredients.lean#L72-L85
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/JohnIngredients.lean#L72-L85

module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Definitions.Def_BasicResults_JohnIngredients
set_option autoImplicit true
@[expose] public section
public section
open scoped InnerProductSpace ComplexConjugate

theorem one_sub_two_mul_sum_sq_le_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1 / 2) (hsum : ∑ i ∈ s, a i = 0) :
    1 - 2 * ∑ i ∈ s, a i ^ 2 ≤ ∏ i ∈ s, (1 + a i) := by sorry
