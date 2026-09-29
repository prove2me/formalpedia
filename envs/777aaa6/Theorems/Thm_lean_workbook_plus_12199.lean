-- Prove2me | Theorems.Thm_lean_workbook_plus_12199
-- name    : lean_workbook_plus_12199
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/ec2de2a7-9526-4b33-aa11-6e5ecbec3dc5
-- statement:
--   Proof for $ a^{2}(1-a)\le\frac{4}{27}$ . If $ 1-a<0$ , the inequality is obvious. Otherwise, $ \frac{ (2-2a)+a+a}{3}\ge\sqrt[3]{2(1-a)(a)(a)}$ , as desired.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12199  (a : ℝ)
  (h₀ : 0 ≤ a)
  (h₁ : a ≤ 1) :
  a^2 * (1 - a) ≤ (4:ℝ) / 27   :=  by sorry
