-- Prove2me | Theorems.Thm_lean_workbook_plus_50448
-- name    : lean_workbook_plus_50448
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/97dac2ba-ee19-4517-8131-0dc93e68cb56
-- statement:
--   Suppose $ a<462$ . If $ a$ and $ 462$ are coprime, or $ (462,a)=1$ then $ a+462$ should be coprime too, by the Euclidean Algorithm.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50448 (a : ℕ) (h : a < 462) (ha : Nat.Coprime 462 a) : Nat.Coprime 462 (a + 462)   :=  by sorry
