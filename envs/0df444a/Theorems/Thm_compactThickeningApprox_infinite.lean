-- Prove2me | Theorems.Thm_compactThickeningApprox_infinite
-- name    : compactThickeningApprox_infinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:43.64693+00:00
-- url     : https://prove2.me/theorems/c1ea9e97-0237-5a5f-b55c-5e04331bc28c
-- title:
--   compact Thickening Approx infinite: compact Thickening Approx infinite
-- statement:
--   A closed thickening of a nonempty planar set at the positive approximation
--   radius contains a nondegenerate closed disk, hence is infinite.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CompactThickeningApprox.lean#L41-L52
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CompactThickeningApprox.lean#L41-L52

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
set_option autoImplicit false
open Metric Set

theorem compactThickeningApprox_infinite (K : Set ℂ) (n : ℕ)
    (hnonempty : K.Nonempty) : (compactThickeningApprox K n).Infinite := by sorry
