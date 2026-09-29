-- Prove2me | Theorems.Thm_lean_workbook_plus_41521
-- name    : lean_workbook_plus_41521
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/cedeec33-2f18-45e8-a691-6bd16487208a
-- statement:
--   Prove that for any positive integer $n$, $S(n) = \sum_{i=1}^{2^{n-1}} (2i-1)^{2i-1} \equiv 2^n \pmod{2^{n+1}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41521 : ∀ n : ℕ, (∑ i in Finset.range (2^(n-1)), (2*i-1)^(2*i-1)) % (2^(n+1)) = 2^n   :=  by sorry
