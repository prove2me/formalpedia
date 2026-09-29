-- Prove2me | Theorems.Thm_lean_workbook_plus_29508
-- name    : lean_workbook_plus_29508
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f7c8388e-d86d-4486-a81b-d9328c2fc750
-- statement:
--   Let the three 2-digit numbers be $\overline{ab}$ , $\overline{cd}$ , $\overline{ef}$ . Then their sum is $10(a+c+e)+(d+e+f)$ . Notice that the order of $a$ , $c$ , and $e$ do not matter (same applies to $d$ , $e$ , and $f$ ); we just need to choose three digits to be $a$ , $c$ , and $e$ , and the remaining digits will be $d$ , $e$ , and $f$ . The number of ways to do this is ${6\choose 3} = \boxed{20}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29508 (Nat.choose 6 3) = 20   :=  by sorry
