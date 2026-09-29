-- Prove2me | Theorems.Thm_lean_workbook_plus_28806
-- name    : lean_workbook_plus_28806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/4e2a8639-547e-4064-851d-8bbaea8a508e
-- statement:
--   Prove the following lemma: If $g$ and $h$ are elements of a group $G$ which commute with each other, and they have relatively prime orders $m,n$ respectively, then the order of the product $gh$ is $mn$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28806 {G : Type*} [Group G] {g h : G} (hg : IsOfFinOrder g) (hh : IsOfFinOrder h) (hgh : Commute g h) (hmn : Nat.Coprime (orderOf g) (orderOf h)) : orderOf (g * h) = (orderOf g) * (orderOf h)   :=  by sorry
