-- Prove2me | Theorems.Thm_lean_workbook_plus_44874
-- name    : lean_workbook_plus_44874
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/5498bf67-acfb-43d9-85cf-bec095337a89
-- statement:
--   Find the greatest integer not exceeding $A$ , where $A=\frac{1}{\sqrt[3]{4}}+\frac{1}{\sqrt[3]{5}}+\frac{1}{\sqrt[3]{6}}+\cdots+\frac{1}{\sqrt[3]{216}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44874 : ∃ k : ℤ, k ≤ A ∧ ∀ l : ℤ, l > k → l ≤ A   :=  by sorry
