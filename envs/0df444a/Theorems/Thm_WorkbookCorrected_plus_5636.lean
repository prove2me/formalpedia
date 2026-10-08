-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_5636
-- name    : WorkbookCorrected.plus_5636
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T20:55:32.709993+00:00
-- url     : https://prove2.me/theorems/3f41a0ac-855d-4ed8-9869-8fce5847d24b
-- title:
--   Binomial coefficient identity #5636
-- statement:
--   The elementary natural-number identity
--   $$
--   \binom{10}{2} * 2^8 = 11520
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_5636`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the combinatorial/arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 23040).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_5636 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_5636; Apache-2.0; corrects Open node e7a2dd95-8da2-48a1-9c74-70fc43cb1b1a

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_5636 : (Nat.choose 10 2) * 2 ^ 8 = 11520 := by sorry
