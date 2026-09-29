-- Prove2me | Theorems.Thm_lean_workbook_plus_471
-- name    : lean_workbook_plus_471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/b0f6a0db-2356-4745-a54e-772da8a51471
-- statement:
--   Lastly, we oversubtracted the case where the number is divisible by all three, so we need to add this back. The product of the three prime factors is $42$ , so we have $\lfloor750/42\rfloor=17$ . Finally, we have $732-213+17=536$ numbers below 750 that are divisible by $2$ , $3$ , or $7$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_471 :
  Finset.card (Finset.filter (λ x => 2 ∣ x ∨ 3 ∣ x ∨ 7 ∣ x) (Finset.range 750)) = 536   :=  by sorry
