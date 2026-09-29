-- Prove2me | Theorems.Thm_lean_workbook_plus_42280
-- name    : lean_workbook_plus_42280
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d409ef9c-bf0b-4a5b-a172-cc40127c0d8f
-- statement:
--   By Cauchy: $(a^2b^2+b^2c^2+c^2a^2)(b+c+a) \geq (ab\sqrt{b}+bc\sqrt{c}+ca\sqrt{a})^2$ So we want to prove $3 \geq (a^2b^2+b^2c^2+c^2a^2) $ Homogenizing: $(a+b+c)^4 \geq 27 (a^2b^2+b^2c^2+c^2a^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42280 :  ∀ a b c : ℝ, (a + b + c)^4 ≥ 27 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)   :=  by sorry
