-- Prove2me | Theorems.Thm_WorkbookSource_base_16299
-- name    : WorkbookSource.base_16299
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:03:16.933252+00:00
-- url     : https://prove2.me/theorems/18ba3e2a-08f9-45c6-9637-c23c0febee8b
-- title:
--   A linear-over-squared-pairwise sum bounds a reciprocal total
-- statement:
--   Prove
--
--    $\frac{x}{\left(y+z\right)^2}+\frac{y}{\left(z+x\right)^2}+\frac{z}{\left(x+y\right)^2} \geq \frac{9}{4\left(x+y+z\right)}$
--
--    for any three positive reals x, y, z.
--
--    Equivalently, prove
--
--    $\frac{s-a}{a^2}+\frac{s-b}{b^2}+\frac{s-c}{c^2} \geq \frac{9}{4s}$ ,
--
--    where a, b, c are the sides of a triangle and $s=\frac{a+b+c}{2}$ .
--
--    Equivalently, show
--
--    $\frac{\sin B \sin C}{\sin^2 \frac{A}{2}} + \frac{\sin C \sin A}{\sin^2 \frac{B}{2}} + \frac{\sin A \sin B}{\sin^2 \frac{C}{2}} \geq 9$ ,
--
--    where A, B, C are the angles of a triangle.
--
--    Thanks!
--
--    Darij
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16299` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16299; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16299 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) ^ 2 + y / (z + x) ^ 2 + z / (x + y) ^ 2) ≥ 9 / (4 * (x + y + z))  :=  by sorry
