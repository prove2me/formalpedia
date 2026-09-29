-- Prove2me | Theorems.Thm_lean_workbook_plus_40975
-- name    : lean_workbook_plus_40975
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/32d864fb-1953-4c79-8a8c-3c990d8eb8b1
-- statement:
--   Suppose $a,b,c$ are real numbers such that $a+b \ge 0, b+c \ge 0$ , and $c+a \ge 0$ . Prove that $a+b+c \ge \frac{|a|+|b|+|c|}{3}$ . (Note: $|x|$ is called the absolute value of $x$ and is defined as follows. If $x \ge 0$ then $|x|= x$ , and if $x < 0$ then $|x| = -x$ . For example, $|6|= 6, |0| = 0$ and $|-6| = 6$ .)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40975 (a b c : ℝ) (h1 : a + b ≥ 0) (h2 : b + c ≥ 0) (h3 : c + a ≥ 0) : a + b + c ≥ (|a| + |b| + |c|) / 3   :=  by sorry
