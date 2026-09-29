-- Prove2me | Theorems.Thm_WorkbookSource_plus_17740
-- name    : WorkbookSource.plus_17740
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:45:42.615294+00:00
-- url     : https://prove2.me/theorems/3dfa1d46-46d0-477f-ac56-6b08e7dafa7b
-- title:
--   An equivalent condition for infinitely many occurrences
-- statement:
--   We say that $P(n)$ is true infinitely often iff for all $N,$ there exists some $n>N$ such that $P(n)$ is true.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_17740` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_17740; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_17740 (P : ℕ → Prop) : (∀ N, ∃ n > N, P n) ↔ ¬ (∃ N, ∀ n > N, ¬ P n)   :=  by sorry
