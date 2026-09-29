-- Prove2me | Theorems.Thm_lean_workbook_plus_17203
-- name    : lean_workbook_plus_17203
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/1b358d11-e58f-46aa-85e3-67033eee6598
-- statement:
--   Let $ H_1, H_2$ be two normal subgroups of $ G$ . Show that $ H_1\cap H_2$ is normal.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17203 {G : Type*} [Group G] {H1 H2 : Subgroup G}
  (h1 : H1.Normal) (h2 : H2.Normal) : (H1 ⊓ H2).Normal   :=  by sorry
