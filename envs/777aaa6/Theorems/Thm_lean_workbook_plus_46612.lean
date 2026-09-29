-- Prove2me | Theorems.Thm_lean_workbook_plus_46612
-- name    : lean_workbook_plus_46612
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/8c6f27d7-45fd-480e-bad8-77ad79579177
-- statement:
--   note that $((2p)!/(p!)^2)=C^{2p}_p$ , which is equivalent to finding the coefficient of $x^p$ in $(1+x)^{2p}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46612 {p : ℕ} (hp : Nat.Prime p) : (Nat.factorial (2 * p) / (Nat.factorial p) ^ 2) = (Nat.choose (2 * p) p)   :=  by sorry
