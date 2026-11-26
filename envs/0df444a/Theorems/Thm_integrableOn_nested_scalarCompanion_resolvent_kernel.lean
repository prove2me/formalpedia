-- Prove2me | Theorems.Thm_integrableOn_nested_scalarCompanion_resolvent_kernel
-- name    : integrableOn_nested_scalarCompanion_resolvent_kernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:56:27.880088+00:00
-- url     : https://prove2.me/theorems/6c38fe85-9f66-51bc-a102-2d54b03b98d0
-- title:
--   integrable On nested scalar Companion resolvent kernel: integrable On nested scalar Companion resolvent kernel
-- statement:
--   For two nested smooth Jordan domains, the derivative-weighted
--   scalar-companion/resolvent kernel is integrable on the parameter square.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L265-L345
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L265-L345

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem integrableOn_nested_scalarCompanion_resolvent_kernel
    (A : E →L[ℂ] E) (Omega Psi : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hnest : closure Omega.carrier ⊆ Psi.carrier) :
    MeasureTheory.IntegrableOn (fun x : ℝ × ℝ =>
      deriv Omega.boundaryParam x.1 •
        (deriv Psi.boundaryParam x.2 •
          (star (Polynomial.eval (Psi.boundaryParam x.2) p) •
            ((2 * (Real.pi : ℂ) * I)⁻¹ •
              ((Psi.boundaryParam x.2 - Omega.boundaryParam x.1)⁻¹ •
                resolvent A (Omega.boundaryParam x.1))))))
      (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ
        uIoc (0 : ℝ) (2 * Real.pi)) := by sorry
