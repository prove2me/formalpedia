-- Prove2me | Theorems.Thm_lean_workbook_plus_74616
-- name    : lean_workbook_plus_74616
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/264dbb2f-7b3a-4762-8aa1-f4787dc7fd44
-- statement:
--   Prove that, if $p$ , $q$ and $r$ are logical statements then \n\n $\left(p\longrightarrow q\vee r\right)\longleftrightarrow\left(\left(p\longrightarrow q\right)\vee\left(p\longrightarrow r\right)\right)$ where $\longrightarrow$ stands for the logical implication and $\longleftrightarrow$ for the logical bi-implication (aka. equivalence).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74616 (p q r : Prop) : (p → q ∨ r) ↔ (p → q) ∨ (p → r)   :=  by sorry
