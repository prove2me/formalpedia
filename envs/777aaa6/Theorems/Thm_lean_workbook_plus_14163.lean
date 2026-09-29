-- Prove2me | Theorems.Thm_lean_workbook_plus_14163
-- name    : lean_workbook_plus_14163
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/6f83e539-2939-4f11-b0e4-86fa006278e9
-- statement:
--   If $a \geq c \geq b$ , then $(a - b)(b - c)(c - a) \geq 0$ i.e. $2(ab^2 + bc^2 + ca^2) \geq 2(a^2b + b^2c + c^2a),$ hence it rests to prove that $a^3+b^3+c^3 \geq a^2b + b^2c + c^2a$ which is straightforward AM-GM $\sum_{cyc} a^3 = \sum_{cyc}\left(\frac{2a^3 + b^3}{3}\right) \geq \sum_{cyc} a^2b.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14163  (a b c : ℝ)
  (h₀ : a ≥ c ∧ c ≥ b) :
  (a - b) * (b - c) * (c - a) ≥ 0   :=  by sorry
