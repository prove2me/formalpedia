-- Prove2me | Theorems.Thm_lean_workbook_plus_62328
-- name    : lean_workbook_plus_62328
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/a7e7f145-d61c-495d-8c18-3af1126e5d4a
-- statement:
--   For every positive integer $m\le n$ , there are exactly $\left \lfloor{\frac{n}{m}}\right \rfloor$ positive integers $a\le n$ such that $m |a$ . Therefore the desired sum is equivalent to, $\sum_{k=1}^{n} {\sigma(k)}=\sum_{m=1}^{n} {\left \lfloor{\frac{n}{m}}\right \rfloor \cdot m}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62328 : ∀ n, ∑ k in Finset.filter (λ k => k ∣ n) (Finset.Icc 1 n), k = ∑ m in Finset.Icc 1 n, (n / m) * m   :=  by sorry
