-- Prove2me | Theorems.Thm_WorkbookSource_base_10724
-- name    : WorkbookSource.base_10724
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:01.749033+00:00
-- url     : https://prove2.me/theorems/69bf8520-d49c-439a-a9e0-18965c09e346
-- title:
--   A product of three quadratic forms bounds a cube
-- statement:
--   It's Holder in the form $(x^2+xy+y^2)(z^2+y^2+yz)(zx+x^2+z^2) \ge (zx+xy+yz)^3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10724` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10724; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10724 {x y z : ℝ} : (x^2 + x*y + y^2)*(z^2 + y^2 + y*z)*(z*x + x^2 + z^2) ≥ (z*x + x*y + y*z)^3  :=  by sorry
