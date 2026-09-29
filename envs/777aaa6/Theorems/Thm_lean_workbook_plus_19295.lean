-- Prove2me | Theorems.Thm_lean_workbook_plus_19295
-- name    : lean_workbook_plus_19295
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/59301e47-3049-496e-af2b-69156016b582
-- statement:
--   $b^3-4bc+c^3=-1$ . Multiplying 27 and adding 64 to both sides we get $27b^3+27c^3-108bc+64=37$ . The LHS can be factored(since it is of the form $a^3+b^3+c^3-3abc$ as $(3b+3c+4)(9b^2+9c^2+16-9c-12b-12c)=37$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19295  (b c : ℤ)
  (h₀ : b^3 - 4 * b * c + c^3 = -1) :
  27 * b^3 + 27 * c^3 - 108 * b * c + 64 = 37   :=  by sorry
