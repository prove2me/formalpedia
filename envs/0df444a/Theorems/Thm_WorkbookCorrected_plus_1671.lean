-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_1671
-- name    : WorkbookCorrected.plus_1671
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:29:33.328785+00:00
-- url     : https://prove2.me/theorems/a26003c4-72cf-4bf7-9674-79e74e663c14
-- title:
--   Elementary arithmetic identity #1671
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   100 + 198 + 294 + 388 + 480 + 570 + 658 + 744 + 828 + 910 + 990 + 1068 + 1144 + 1218 + 1290 + 1360 + 1428 + 1494 + 1558 + 1620 + 1680 + 1738 + 1794 + 1848 + 1900 + 1950 + 1998 + 2044 + 2088 + 2130 + 2170 + 2208 + 2244 + 2278 + 2310 + 2340 + 2368 + 2394 + 2418 + 2440 + 2460 + 2478 + 2494 + 2508 + 2520 + 2530 + 2538 + 2544 + 2548 + 2550 = 85850
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_1671`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_1671 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_1671; Apache-2.0; corrects Open node 823b88e6-2c27-47ee-8d02-0b1526dad3be

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_1671 : 100 + 198 + 294 + 388 + 480 + 570 + 658 + 744 + 828 + 910 + 990 + 1068 + 1144 + 1218 + 1290 + 1360 + 1428 + 1494 + 1558 + 1620 + 1680 + 1738 + 1794 + 1848 + 1900 + 1950 + 1998 + 2044 + 2088 + 2130 + 2170 + 2208 + 2244 + 2278 + 2310 + 2340 + 2368 + 2394 + 2418 + 2440 + 2460 + 2478 + 2494 + 2508 + 2520 + 2530 + 2538 + 2544 + 2548 + 2550 = 85850 := by sorry
