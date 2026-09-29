-- Prove2me | Theorems.Thm_lean_workbook_plus_45671
-- name    : lean_workbook_plus_45671
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/dcfc06d0-55c8-4668-9c90-01135a03fdac
-- statement:
--   Prove that if $a > b > 0$, then $\sqrt{a} > \sqrt{b}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45671 {a b : ℝ} (hab : a > b) (hb : b > 0) : Real.sqrt a > Real.sqrt b   :=  by sorry
