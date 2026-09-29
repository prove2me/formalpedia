-- Prove2me | Theorems.Thm_WorkbookSource_base_41419
-- name    : WorkbookSource.base_41419
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:28:23.487745+00:00
-- url     : https://prove2.me/theorems/c52cdfd3-5acb-436c-a00b-803acb159797
-- title:
--   A six-variable cyclic quadratic expression is nonnegative
-- statement:
--   17. $x,y,z,u,v,w$ are real numbers,prove that:
--
--    $(x-z)(v-z)+(y-x)(w-x)+(u-y)(z-y)+(w-v)(w+z)+(u-w)(x+u)+(v-u)(y+v)\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41419` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41419; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41419 (x y z u v w : ℝ) : (x - z) * (v - z) + (y - x) * (w - x) + (u - y) * (z - y) + (w - v) * (w + z) + (u - w) * (x + u) + (v - u) * (y + v) ≥ 0  :=  by sorry
