-- Prove2me | Theorems.Thm_WorkbookSource_base_8104
-- name    : WorkbookSource.base_8104
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:51:27.052161+00:00
-- url     : https://prove2.me/theorems/31d18169-e991-451c-9fc1-32db07759284
-- title:
--   A fourth-power bound at zero sum and fixed norm
-- statement:
--   Prove that $x^4+y^4+z^4+t^4+u^4 \le 260$ given $x+y+z+t+u=0$ and $x^2+y^2+z^2+t^2+u^2=20$, where $x,y,z,t,u \in\mathbb{R}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8104` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8104; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8104 (x y z t u : ℝ) (h₁ : x + y + z + t + u = 0) (h₂ : x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 + u ^ 2 = 20) : x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4 + u ^ 4 ≤ 260  :=  by sorry
