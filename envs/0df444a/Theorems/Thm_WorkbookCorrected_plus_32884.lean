-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_32884
-- name    : WorkbookCorrected.plus_32884
-- status  : Open
-- author  : @carlok
-- created : 2026-10-06T20:55:55.346402+00:00
-- url     : https://prove2.me/theorems/4202b75c-c26e-46dc-8aac-688f0092f339
-- title:
--   Binomial coefficient identity #32884
-- statement:
--   The elementary natural-number identity
--   $$
--   (\binom{24}{0} - \binom{24}{2} + \binom{24}{4} - \binom{24}{6} + \binom{24}{8} - \binom{24}{10} + \binom{24}{12} - \binom{24}{14} + \binom{24}{16} - \binom{24}{18} + \binom{24}{20} - \binom{24}{22} + \binom{24}{24}) = 4096
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_32884`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the combinatorial/arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 0).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_32884 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_32884; Apache-2.0; corrects Open node 2309c867-340b-462b-a910-07ded8f1b4ea

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_32884 : ((Nat.choose 24 0) - (Nat.choose 24 2) + (Nat.choose 24 4) - (Nat.choose 24 6) + (Nat.choose 24 8) - (Nat.choose 24 10) + (Nat.choose 24 12) - (Nat.choose 24 14) + (Nat.choose 24 16) - (Nat.choose 24 18) + (Nat.choose 24 20) - (Nat.choose 24 22) + (Nat.choose 24 24)) = 4096 := by sorry
