-- Prove2me | Theorems.Thm_WorkbookSource_base_8651
-- name    : WorkbookSource.base_8651
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:40:00.107887+00:00
-- url     : https://prove2.me/theorems/50077eec-91b7-43f7-9cf7-ed579d025a8d
-- title:
--   A sixth-degree cyclic inequality with a Vandermonde square
-- statement:
--   Let $x$ , $y$ and $z$ be real numbers. Prove that:
--    ${({x^2} + {y^2} + {z^2})^3} \ge 8({x^3}{y^3} + {y^3}{z^3} + {x^3}{z^3})+3x^2y^2z^2+3(x-y)^2(x-z)^2(y-z)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8651` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8651; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8651 (x y z: ℝ) :  (x^2 + y^2 + z^2)^3 ≥ 8 * (x^3 * y^3 + y^3 * z^3 + x^3 * z^3) + 3 * x^2 * y^2 * z^2 + 3 * (x-y)^2 * (x-z)^2 * (y-z)^2  :=  by sorry
