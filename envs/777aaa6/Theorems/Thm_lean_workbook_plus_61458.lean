-- Prove2me | Theorems.Thm_lean_workbook_plus_61458
-- name    : lean_workbook_plus_61458
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/6210b3f3-9f34-4842-b00e-bed319877091
-- statement:
--   An alternative proof: Observe that the group of units $(\mathbb{Z}/d\mathbb{Z})^*$ is a subgroup of $(\mathbb{Z}/n\mathbb{Z})^*$ when $d | n$. Since the order of a subgroup divides the order of the group, $\varphi(d) | \varphi(n)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61458 {d n : ℕ} (h : d ∣ n) : totient d ∣ totient n   :=  by sorry
