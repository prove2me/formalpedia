-- Prove2me | Theorems.Thm_lean_workbook_plus_42412
-- name    : lean_workbook_plus_42412
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/443fbd94-5d6f-4f79-b708-39c27cd0550d
-- statement:
--   Let $ H$ be a subgroup of finite index of an infinite group $ G$ . Prove that $ G$ has a normal subgroup of finite index which is contained in $ H$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42412 (G : Type*) [Group G] [Infinite G]
    (H : Subgroup G) [H.FiniteIndex] : ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ N ≤ H   :=  by sorry
