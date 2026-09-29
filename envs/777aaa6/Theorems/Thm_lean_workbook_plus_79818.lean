-- Prove2me | Theorems.Thm_lean_workbook_plus_79818
-- name    : lean_workbook_plus_79818
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/92d2527b-27f1-4c70-9d58-c9f4596882f1
-- statement:
--   $\left[A,B,C \right]$ denotes symmetric sum. It is $\left[A,B,C \right] = x^Ay^Bz^C+x^Ay^Cz^B+x^By^Az^C+x^By^Cz^A+x^Cy^Az^B+x^Cy^Bz^A$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79818 {x y z : ℕ} {A B C : ℕ} : (x^A * y^B * z^C + x^A * y^C * z^B + x^By^Az^C + x^By^Cz^A + x^Cy^Az^B + x^Cy^Bz^A) = (x^A * y^B * z^C + x^A * y^C * z^B + x^By^Cz^A + x^By^Az^C + x^Cy^Bz^A + x^Cy^Az^B)   :=  by sorry
