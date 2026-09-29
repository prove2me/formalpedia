-- Prove2me | Theorems.Thm_lean_workbook_plus_65859
-- name    : lean_workbook_plus_65859
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6f236ed9-5972-46e5-804b-0e8117a968a5
-- statement:
--   Show that $ A = \{ x<1, y>1 \} $ is open in $ \mathbb{R} \times \mathbb{R} $ (but not the metric space $ \mathbb{R}^2 $ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65859 : IsOpen {p : ℝ × ℝ | p.fst < 1 ∧ p.snd > 1}   :=  by sorry
