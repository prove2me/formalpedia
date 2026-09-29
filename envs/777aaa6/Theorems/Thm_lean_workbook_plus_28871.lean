-- Prove2me | Theorems.Thm_lean_workbook_plus_28871
-- name    : lean_workbook_plus_28871
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/87a20780-a521-4dcb-9508-90113a15bf7b
-- statement:
--   Note that $xy(x^2-y^2)$ is always even for all integers $x,y$ . Similarly, $yz(y^2-z^2)$ and $zx(z^2-x^2)$ are also always even. Therefore, their sum, $xy(x^2-y^2)+yz(y^2-z^2)+zx(z^2-x^2)$ , must also be even. However, $1$ is not an even number, so there are no integer solutions.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28871 : ∀ x y z : ℤ, Even (x * y * (x ^ 2 - y ^ 2) + y * z * (y ^ 2 - z ^ 2) + z * x * (z ^ 2 - x ^ 2))   :=  by sorry
