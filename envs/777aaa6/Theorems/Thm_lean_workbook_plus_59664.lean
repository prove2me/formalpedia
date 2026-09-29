-- Prove2me | Theorems.Thm_lean_workbook_plus_59664
-- name    : lean_workbook_plus_59664
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/98b3c4aa-e511-4af6-ac31-8b7ac2df42ad
-- statement:
--   Let $\overline{xa}$ a number with this property where $x$ is a digit and $a$ is a number with $n$ digits. We have $2\cdot \overline{xa}=\overline{ax}$ $\Leftrightarrow$ $2\cdot 10^n\cdot x+2a=10a+x$ $\Leftrightarrow$ $(2\cdot 10^n-1)\cdot x=8a$ . From which $8\mid x$ , but $x$ is a digit, so $x\in \{0,8\}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59664 (x a : ℕ) (hn: a < 10^n) (hx: x < 10) (h : 2 * (10^n * x + a) = 10 * a + x) : 8 ∣ x   :=  by sorry
