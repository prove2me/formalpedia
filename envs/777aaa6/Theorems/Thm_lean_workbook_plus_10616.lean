-- Prove2me | Theorems.Thm_lean_workbook_plus_10616
-- name    : lean_workbook_plus_10616
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/329d7200-4761-40f5-a601-6616a8cd814e
-- statement:
--   We have $c = -a-b$ and ${a^2} + {b^2} + {c^2} = 1 \Leftrightarrow ab + bc + ca = - \frac{1}{2} \Leftrightarrow ab = - \frac{1}{2} + {c^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10616  (a b c : ℝ)
  (h₀ : c = -(a + b))
  (h₁ : a^2 + b^2 + c^2 = 1) :
  a * b = -1 / 2 + c^2   :=  by sorry
