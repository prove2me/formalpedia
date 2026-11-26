-- Prove2me | Theorems.Thm_card_valid_bases_asymptotic
-- name    : card_valid_bases_asymptotic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:26.94246+00:00
-- url     : https://prove2.me/theorems/f8ee2ced-7492-4e0c-b5f0-cdaf0957898d
-- title:
--   card valid bases asymptotic: card valid bases asymptotic
-- statement:
--   `#(N) ∼ 2^(2^N - N)`: the ratio tends to `1`.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L404-L422
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L404-L422

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
open Filter Topology
omit [Fintype α] [DecidableEq α]

theorem card_valid_bases_asymptotic :
    Tendsto (fun n : ℕ =>
      (Fintype.card (ValidBasis (Fin n)) : ℝ) / (2 : ℝ) ^ (2 ^ n - n))
      atTop (nhds (1 : ℝ)) := by sorry
