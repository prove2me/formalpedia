-- Prove2me | Theorems.Thm_lean_workbook_plus_45835
-- name    : lean_workbook_plus_45835
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c06966be-2295-4f3e-ba63-709eeb6f1716
-- statement:
--   The more general $\left|ab\right|=\left|a\right|\left|b\right|$ also holds (the statement $\left|z\right|^2=\left|z^2\right|$ follows by using $a=b=z$ ).\n\nTo see this, observe that $\left|ab\right|^2=\left(ab\right)\left(\overline{ab}\right)=\left(a\overline{a}\right)\left(b\overline{b}\right)=\left|a\right|^2\left|b\right|^2,$ so since magnitudes are nonnegative, $\left|ab\right|=\left|a\right|\left|b\right|$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45835 (a b : ℂ) : ‖a * b‖ = ‖a‖ * ‖b‖   :=  by sorry
