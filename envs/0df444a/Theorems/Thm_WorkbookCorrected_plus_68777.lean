-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_68777
-- name    : WorkbookCorrected.plus_68777
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:14:22.605177+00:00
-- url     : https://prove2.me/theorems/cf84f1e1-e319-41e9-88da-d7cd3e43b3e1
-- title:
--   Euler totient of 462 is 120
-- statement:
--   Euler's totient function satisfies $\varphi(462)=120$: there are $120$ integers in $\{1,\ldots,461\}$ coprime to $462$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_68777`, whose preamble lacked the totient import.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_68777 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_68777; Apache-2.0; corrects Open node a93df8b9-2e87-4bb7-a25f-029eb34d24d8

import Mathlib.Data.Nat.Totient

theorem WorkbookCorrected.plus_68777 : Nat.totient 462 = 120 := by sorry
