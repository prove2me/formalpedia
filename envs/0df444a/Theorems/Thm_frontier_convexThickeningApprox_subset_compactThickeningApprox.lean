-- Prove2me | Theorems.Thm_frontier_convexThickeningApprox_subset_compactThickeningApprox
-- name    : frontier_convexThickeningApprox_subset_compactThickeningApprox
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:01.39992+00:00
-- url     : https://prove2.me/theorems/0b466a3a-c359-47d2-bf04-af22342ea5a9
-- title:
--   frontier convex Thickening Approx subset compact Thickening Approx: frontier convex Thickening Approx subset compact Thickening Approx
-- statement:
--   The frontier of the open thickening at stage `n` lies in the closed
--   thickening at the same radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CompactThickeningApprox.lean#L94-L98
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CompactThickeningApprox.lean#L94-L98

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
set_option autoImplicit false
open Metric Set

theorem frontier_convexThickeningApprox_subset_compactThickeningApprox
    (K : Set ℂ) (n : ℕ) :
    frontier (convexThickeningApprox K n) ⊆ compactThickeningApprox K n := by sorry
