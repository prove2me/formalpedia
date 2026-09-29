-- Prove2me | Theorems.Thm_WorkbookSource_problem_28330
-- name    : WorkbookSource.problem_28330
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:50.827933+00:00
-- url     : https://prove2.me/theorems/96718473-2fa2-48b4-b0b7-25013e690b92
-- title:
--   Equivalent cyclic fraction identities
-- statement:
--   Let $x,y,z>0$ and $x^2+y^2+z^2+2xyz=1.$ Prove that $$\frac{xy}{xy+z}+\frac{yz}{yz+x}+\frac{zx}{zx+y}=1$$ $$\iff$$ $$\frac{x}{x+yz}+\frac{y}{y+zx}+\frac{z}{z+xy}=2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28330` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28330; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_28330 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 + 2 * x * y * z = 1) : (x * y / (x * y + z) + y * z / (y * z + x) + z * x / (z * x + y) = 1 ↔ x / (x + y * z) + y / (y + z * x) + z / (z + x * y) = 2)  :=  by sorry
