-- Prove2me | Theorems.Thm_lean_workbook_plus_31197
-- name    : lean_workbook_plus_31197
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e32f7cbf-a739-47e5-b199-3b35d6718dcb
-- statement:
--   Prove that: \n $ \frac {1}{{{a^4} + {a^2}{b^2} + {b^4}}} + \frac {1}{{{b^4} + {b^2}{c^2} + {c^4}}} + \frac {1}{{{c^4} + {c^2}{a^2} + {a^4}}} \ge \frac {9}{{\left( {{a^2} + {b^2} + {c^2}} \right)\left( {ab + bc + ca} \right)}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31197 : ∀ a b c : ℝ, (1 / (a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4) + 1 / (b ^ 4 + b ^ 2 * c ^ 2 + c ^ 4) + 1 / (c ^ 4 + c ^ 2 * a ^ 2 + a ^ 4)) ≥ 9 / ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a))   :=  by sorry
