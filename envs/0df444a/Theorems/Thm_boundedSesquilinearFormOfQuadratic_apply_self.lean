-- Prove2me | Theorems.Thm_boundedSesquilinearFormOfQuadratic_apply_self
-- name    : boundedSesquilinearFormOfQuadratic_apply_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:58.653864+00:00
-- url     : https://prove2.me/theorems/52c85eac-7742-4b7d-8316-25756c50392e
-- title:
--   bounded Sesquilinear Form Of Quadratic apply self: bounded Sesquilinear Form Of Quadratic apply self
-- statement:
--   The polarized sesquilinear form recovers the quadratic function on its diagonal.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Polarization.lean#L373-L376
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Polarization.lean#L373-L376

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Spectral_Spectral_Polarization
set_option autoImplicit false
open scoped ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (q : V → ℝ)
variable (hq_smul : ∀ (c : ℂ) (x : V), q (c • x) = ‖c‖ ^ 2 * q x)
variable (hq_para : ∀ x y : V,
  q (x + y) + q (x - y) = (q x + q x) + (q y + q y))
include hq_smul
omit hq_smul
include hq_para
include hq_smul
omit hq_para
include hq_para
variable (hq_nonneg : ∀ x : V, 0 ≤ q x)
include hq_nonneg
variable (hq_le : ∀ x : V, q x ≤ ‖x‖ ^ 2)
include hq_le
omit hq_para hq_nonneg hq_le
include hq_para hq_nonneg hq_le

theorem boundedSesquilinearFormOfQuadratic_apply_self (x : V) :
    boundedSesquilinearFormOfQuadratic q hq_smul hq_para hq_nonneg hq_le x x = q x := by sorry
