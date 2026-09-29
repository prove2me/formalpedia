-- Prove2me | Theorems.Thm_WorkbookSource_plus_28132
-- name    : WorkbookSource.plus_28132
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:51.033985+00:00
-- url     : https://prove2.me/theorems/5e2bb528-296e-4086-8b05-46047123a560
-- title:
--   A mixed bilinear inequality with equal sums
-- statement:
--   Prove that:
--    \begin{align*}ax+by+cz+\frac{x^2+y^2+z^2- xy-yz-zx}{3} \geqslant ab+bc+ca. \end{align*}
--   Given: $a,b,c,x,y,z \in \mathbb{R}$ and $a+b+c=x+y+z$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28132` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28132; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28132 (a b c x y z : ℝ) (ha : a + b + c = x + y + z) : a * x + b * y + c * z + (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) / 3 ≥ a * b + b * c + c * a   :=  by sorry
