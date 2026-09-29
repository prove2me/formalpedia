-- Prove2me | Theorems.Thm_lean_workbook_plus_40462
-- name    : lean_workbook_plus_40462
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d1d84009-0265-448e-a5c1-13acbbf33b1b
-- statement:
--   It suffices to prove that $ \frac {1}{{{a^3} + {b^2} + {c^2}}} + \frac {1}{{{b^3} + {c^2} + {a^2}}} + \frac {1}{{{c^3} + {a^2} + {b^2}}} \le \frac {3}{{{a^2} + {b^2} + {c^2}}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40462 : ∀ a b c : ℝ, (1 / (a ^ 3 + b ^ 2 + c ^ 2) + 1 / (b ^ 3 + c ^ 2 + a ^ 2) + 1 / (c ^ 3 + a ^ 2 + b ^ 2) ≤ 3 / (a ^ 2 + b ^ 2 + c ^ 2))   :=  by sorry
