-- Prove2me | Theorems.Thm_lean_workbook_plus_30144
-- name    : lean_workbook_plus_30144
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f4cb1693-2212-4155-a842-0b92651220f0
-- statement:
--   Let $a=x+5$ , $b=y+5$ , and $c=z+5$ . Then $a+b+c=15$ . You can solve this by stars and bars easily, as $a,b,c\ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30144 ∀ x y z : ℕ, x + y + z = 5 → (x + 5) + (y + 5) + (z + 5) = 15   :=  by sorry
