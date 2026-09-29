-- Prove2me | Theorems.Thm_lean_workbook_plus_77697
-- name    : lean_workbook_plus_77697
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/7c1a6492-9a5b-47ba-bbc7-b9b6b62453c1
-- statement:
--   Determine whether or not the relation $m \sim n$ in $\mathbb{Z}$ if $m \equiv n \text{ }(\text{mod }6)$ is an equivalence relation on $\mathbb{Z}$. If it is, describe the partition given by it. If not, state why it fails to be one.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77697 : Equivalence (ModEq 6)  :=  by sorry
