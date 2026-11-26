-- Prove2me | Theorems.Thm_polynomialSupNorm_affineComposition_closedBall
-- name    : polynomialSupNorm_affineComposition_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:32.407088+00:00
-- url     : https://prove2.me/theorems/66cc6a71-0e79-5fd6-9aa9-24eebfa92104
-- title:
--   polynomial Sup Norm affine Composition closed Ball: polynomial Sup Norm affine Composition closed Ball
-- statement:
--   Precomposing with `z ↦ R * z + c` transports the polynomial sup-norm from the unit closed
--   disk to `closedBall c R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineDisk.lean#L27-L36
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineDisk.lean#L27-L36

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_AffineDisk
set_option autoImplicit false
open scoped InnerProductSpace Pointwise Polynomial

theorem polynomialSupNorm_affineComposition_closedBall
    (p : ℂ[X]) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    polynomialSupNorm (p.affineComposition (R : ℂ) c)
        (Metric.closedBall (0 : ℂ) 1) =
      polynomialSupNorm p (Metric.closedBall c R) := by sorry
