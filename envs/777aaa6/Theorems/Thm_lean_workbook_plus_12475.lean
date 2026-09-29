-- Prove2me | Theorems.Thm_lean_workbook_plus_12475
-- name    : lean_workbook_plus_12475
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0dd8ab5b-0fd7-45ed-a4c2-0ecae243a6db
-- statement:
--   Now, we want to find $2^{30} \pmod{1000}$ . All congruences here will be in $\pmod{1000}$ . We note that $2^{10} = 1024 \equiv 24$ . Now our problem has turned into $24^3$ . There may be some clever way to evaluate this, but it isn't that tedious to just multiply out, knowing that $24^2 = 576$ . We get $24^3 = 13824 \equiv \boxed{824}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12475 :
  (2^30) % 1000 = 824   :=  by sorry
