-- Prove2me | Theorems.Thm_lean_workbook_plus_35148
-- name    : lean_workbook_plus_35148
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c094b4b9-d4e6-46c9-b0c3-9232d164808d
-- statement:
--   There are two straightforward ways to do this. I will give both. Method 2- Complementary Counting: count what we don't want. There are $\binom{10}{4}=210$ total ways to choose $4$ books. We don't want exactly $0$ biographies or $1$ biography. If we get $0$ biographies, there are $\binom{6}{4}=15$ ways to choose the novels. If we get $1$ biography, there $\binom{4}{1}=4$ ways to get the biographies, and $\binom{6}{3}=20$ ways to choose the novel for a total of $80$ . So, we have $15+80=95$ ways to choose what we don't want. This means that there are $210-95=\boxed{115}$ combinations we do want.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35148 (Nat.choose 10 4) - (Nat.choose 6 4 + Nat.choose 4 1 * Nat.choose 6 3) = 115   :=  by sorry
