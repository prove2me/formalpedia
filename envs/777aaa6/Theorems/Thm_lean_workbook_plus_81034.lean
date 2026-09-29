-- Prove2me | Theorems.Thm_lean_workbook_plus_81034
-- name    : lean_workbook_plus_81034
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2244cc0d-1c65-4524-a4c1-d250e85997c9
-- statement:
--   An easy extension. Let $z_1 , z_2 \in \mathbb{C}$ so that $\left\{\begin{array}{ccc}az_1 ^2 + z_2 ^2 & = & r \\ z_1 \left(az_1 ^2 - 3z_2 ^2\right) & = & b\\ z_2 \left(z_2 ^2-3az_1^2\right) & = & c\end{array}\right\|$ , where $\{r,a,b,c\}\subset\mathbb R^*$ . Prove that $r^3=c^2+ab^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81034 (a b c r : ℝ) (z1 z2 : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hr : r ≠ 0) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (ha' : (a:ℂ) ≠ 0) (hb' : (b:ℂ) ≠ 0) (hc' : (c:ℂ) ≠ 0) (hr' : (r:ℂ) ≠ 0) (hz1' : (z1:ℂ) ≠ 0) (hz2' : (z2:ℂ) ≠ 0) : a * z1 ^ 2 + z2 ^ 2 = r ∧ z1 * (a * z1 ^ 2 - 3 * z2 ^ 2) = b ∧ z2 * (z2 ^ 2 - 3 * a * z1 ^ 2) = c → r ^ 3 = c ^ 2 + a * b ^ 2   :=  by sorry
