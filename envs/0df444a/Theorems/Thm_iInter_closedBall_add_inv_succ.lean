-- Prove2me | Theorems.Thm_iInter_closedBall_add_inv_succ
-- name    : iInter_closedBall_add_inv_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:38.575636+00:00
-- url     : https://prove2.me/theorems/026c354d-0e69-5385-89bd-c8dfd805338e
-- title:
--   i Inter closed Ball add inv succ: i Inter closed Ball add inv succ
-- statement:
--   The closed disks `closedBall c (r + 1 / (n + 1))` intersect to `closedBall c r`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L114-L125
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L114-L125

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]

theorem iInter_closedBall_add_inv_succ (c : ℂ) (r : ℝ) :
    (⋂ n : ℕ, Metric.closedBall c (r + 1 / ((n : ℝ) + 1))) = Metric.closedBall c r := by sorry
