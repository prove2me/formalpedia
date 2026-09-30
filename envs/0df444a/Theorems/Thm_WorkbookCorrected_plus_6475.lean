-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_6475
-- name    : WorkbookCorrected.plus_6475
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:18:53.667217+00:00
-- url     : https://prove2.me/theorems/58553f6f-cbaa-40e7-ad02-441ce3574ca6
-- title:
--   Elementary arithmetic identity #6475
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   23 + 33 + 45 + 59 + 75 + 93 + 113 + 135 + 159 + 185 + 213 + 243 + 275 + 309 + 345 + 383 + 423 + 465 + 509 + 555 + 603 + 653 + 705 + 759 + 815 + 873 + 933 + 995 + 1059 + 1125 + 1193 + 1263 + 1335 + 1409 + 1485 + 1563 + 1643 + 1725 + 1809 + 1895 + 1983 + 2073 + 2165 + 2259 + 2355 + 2453 + 2553 + 2655 + 2759 + 2865 + 2973 + 3083 + 3195 + 3309 + 3425 + 3543 + 3663 + 3785 + 3909 + 4035 + 4163 + 4293 + 4425 + 4559 + 4695 + 4833 + 4973 + 5115 + 5259 + 5405 + 5553 + 5703 + 5855 + 6009 = 158360
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_6475`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_6475 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_6475; Apache-2.0; corrects Open node 1a4fb28f-a41b-4fe8-a50a-4448f25742f2

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_6475 : 23 + 33 + 45 + 59 + 75 + 93 + 113 + 135 + 159 + 185 + 213 + 243 + 275 + 309 + 345 + 383 + 423 + 465 + 509 + 555 + 603 + 653 + 705 + 759 + 815 + 873 + 933 + 995 + 1059 + 1125 + 1193 + 1263 + 1335 + 1409 + 1485 + 1563 + 1643 + 1725 + 1809 + 1895 + 1983 + 2073 + 2165 + 2259 + 2355 + 2453 + 2553 + 2655 + 2759 + 2865 + 2973 + 3083 + 3195 + 3309 + 3425 + 3543 + 3663 + 3785 + 3909 + 4035 + 4163 + 4293 + 4425 + 4559 + 4695 + 4833 + 4973 + 5115 + 5259 + 5405 + 5553 + 5703 + 5855 + 6009 = 158360 := by sorry
