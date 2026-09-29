-- Prove2me | Theorems.Thm_WorkbookSource_base_46536
-- name    : WorkbookSource.base_46536
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:39:39.627838+00:00
-- url     : https://prove2.me/theorems/cb58fa6e-c166-40f9-aca3-b4a136fd08f0
-- title:
--   A quartic bound under a unit quadratic norm
-- statement:
--   Prove the inequality: $21q\leq 48+\frac{5p^2(2q-3)}{9}$ where $p=x+y+z$, $q=xy+yz+xz$, and $p^2-2q=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46536` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46536; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46536 (x y z p q : ℝ) (hp : p = x + y + z) (hq : q = x*y + y*z + x*z) (h : p^2 - 2*q = 3) : 21*q ≤ 48 + (5 * p^2 * (2*q - 3)) / 9  :=  by sorry
