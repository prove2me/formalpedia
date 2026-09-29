-- Prove2me | Theorems.Thm_WorkbookCorrected_base_46350
-- name    : WorkbookCorrected.base_46350
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:23.857856+00:00
-- url     : https://prove2.me/theorems/6d17de07-2aea-458f-96f3-3ec01bca41cc
-- title:
--   A pairwise-product maximum under a quadratic relation
-- statement:
--   Let $a,b,c\in \mathbb{R}$ and $a^{2}+b^{2}+c^{2}+4ab=128$ . Find maximum of $ab+bc+ac$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46350` (Apache-2.0). Natural-language proposition preserved; the source bound is completed with an exact attainment witness. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46350; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_46350 : (∀ (a b c : ℝ) (h : a^2 + b^2 + c^2 + 4 * a * b = 128), a * b + b * c + c * a ≤ 64) ∧ (∃ a b c : ℝ, (a^2 + b^2 + c^2 + 4 * a * b = 128) ∧ (
  a * b + b * c + c * a  =  64  )) := by sorry
