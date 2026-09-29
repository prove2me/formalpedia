-- Prove2me | Theorems.Thm_lean_workbook_plus_62844
-- name    : lean_workbook_plus_62844
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/1ea39204-06b8-4193-bdf3-98b38429275d
-- statement:
--   Suppose $d \vert n$ , where $d$ and $n$ are positive integers. Write $n = dk$ and let $y = p^d$ . Then the identity $y^k - 1 = (y-1)(y^{k-1} + y^{k-2} + \cdots + 1)$ shows that $p^d - 1$ divides $p^n - 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62844 {d n : ℕ} (h : d ∣ n) (hn : 0 < n) {p : ℕ} (hp : 1 < p) : p^d - 1 ∣ p^n - 1   :=  by sorry
