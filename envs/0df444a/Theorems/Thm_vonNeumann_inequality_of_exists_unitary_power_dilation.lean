-- Prove2me | Theorems.Thm_vonNeumann_inequality_of_exists_unitary_power_dilation
-- name    : vonNeumann_inequality_of_exists_unitary_power_dilation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:34:16.773402+00:00
-- url     : https://prove2.me/theorems/72886c92-8609-4d09-aa80-8211fc3c559c
-- title:
--   von Neumann inequality of exists unitary power dilation: von Neumann inequality of exists unitary power dilation
-- statement:
--   **Von Neumann's inequality** for an operator admitting a unitary power dilation: if there are
--   a Hilbert space `H`, an inner-product-preserving `V : E →L[ℂ] H` and a unitary `U` on `H` with
--   `V† U^n V = T^n` for all `n` (the conclusion of L3.1), then
--   `‖p(T)‖ ≤ sup_{‖z‖ ≤ 1} ‖p(z)‖` for every polynomial `p`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L136-L146
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/VonNeumann.lean#L136-L146

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vonNeumann_inequality_of_exists_unitary_power_dilation (T : E →L[ℂ] E)
    (hdil : ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
      (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      U ∈ unitary (H →L[ℂ] H) ∧
      (∀ (n : ℕ) (x : E), adjoint V ((U ^ n) (V x)) = (T ^ n) x))
    (p : ℂ[X]) :
    ‖aeval T p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by sorry
