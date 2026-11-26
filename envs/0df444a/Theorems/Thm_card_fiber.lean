-- Prove2me | Theorems.Thm_card_fiber
-- name    : card_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:43:54.141344+00:00
-- url     : https://prove2.me/theorems/4344c672-7080-47d3-af16-30fa51372999
-- title:
--   card fiber: card fiber
-- statement:
--   One fiber: bases generating `t` are a power set of redundant opens.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB.lean#L204-L215
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB.lean#L204-L215

import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Sum
import Definitions.Def_CARDB
set_option autoImplicit true
open Set TopologicalSpace
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (t : TopologicalSpace α)
omit [DecidableEq α]

theorem card_fiber :
    Fintype.card (Fiber t) =
      2 ^ (ncard (opensOf t) - ncard (minimalBasis t)) := by sorry
