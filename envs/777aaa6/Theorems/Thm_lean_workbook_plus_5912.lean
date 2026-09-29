-- Prove2me | Theorems.Thm_lean_workbook_plus_5912
-- name    : lean_workbook_plus_5912
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/08faf0be-0ae7-47c5-ade3-3ddcbc1fec0b
-- statement:
--   Find all $(x_1,x_2,x_3) \in \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/3\mathbb{Z} \times \mathbb{Z}/5\mathbb{Z}$ that satisfy $x_1^2 = x_1$, $x_2^2 = x_2$, and $x_3^2 = x_3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5912 (x1 : ZMod 2) (x2 : ZMod 3) (x3 : ZMod 5) (hx1 : x1 ^ 2 = x1) (hx2 : x2 ^ 2 = x2) (hx3 : x3 ^ 2 = x3) : (x1 = 0 ∨ x1 = 1) ∧ (x2 = 0 ∨ x2 = 1) ∧ (x3 = 0 ∨ x3 = 1)   :=  by sorry
