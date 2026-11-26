-- Prove2me | Theorems.Thm_compactThickeningApprox_spec
-- name    : compactThickeningApprox_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:22.690614+00:00
-- url     : https://prove2.me/theorems/e96e67f8-aa93-5813-9988-012a91212cc9
-- title:
--   compact Thickening Approx spec: compact Thickening Approx spec
-- statement:
--   Closed thickenings of a nonempty compact planar set form an antitone
--   sequence of nonempty compact sets whose intersection is exactly the set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CompactThickeningApprox.lean#L56-L90
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CompactThickeningApprox.lean#L56-L90

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
set_option autoImplicit false
open Metric Set

theorem compactThickeningApprox_spec (K : Set ℂ) (hcompact : IsCompact K)
    (hnonempty : K.Nonempty) :
    Antitone (compactThickeningApprox K) ∧
      (∀ n, IsCompact (compactThickeningApprox K n)) ∧
      (∀ n, (compactThickeningApprox K n).Nonempty) ∧
      (⋂ n, compactThickeningApprox K n) = K := by sorry
