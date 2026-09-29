-- Prove2me | Theorems.Thm_lean_workbook_plus_20234
-- name    : lean_workbook_plus_20234
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/e4918c25-0298-4b03-ae38-c14866dcc0e0
-- statement:
--   I believe it should be $ -\dfrac{\pi}{2}\le x\le\dfrac{\pi}{2}$ . You have to be careful with arcsines, because like sin(pi/12)=sin(11pi/12), and we want it to be well defined.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20234 ∀ x, (Real.sin x = Real.cos (x - Real.pi/2)) ∨ (Real.sin x = Real.cos (x + Real.pi/2)) ↔ - Real.pi/2 <= x ∧ x <= Real.pi/2   :=  by sorry
