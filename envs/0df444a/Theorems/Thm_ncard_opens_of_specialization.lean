-- Prove2me | Theorems.Thm_ncard_opens_of_specialization
-- name    : ncard_opens_of_specialization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:43.026417+00:00
-- url     : https://prove2.me/theorems/b98d4bd7-4827-45ff-849d-55ded1a3e7a6
-- title:
--   ncard opens of specialization: ncard opens of specialization
-- statement:
--   The ncard opens of specialization construction uses the ncard opens of specialization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L167-L173
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L167-L173

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

theorem ncard_opens_of_specialization {t : TopologicalSpace α}
    (hne : x ≠ y) (hy : y ∈ minimalOpen t x) :
    ncard (opensOf t) ≤ 3 * 2 ^ (Fintype.card α - 2) := by sorry
