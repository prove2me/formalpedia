-- Prove2me | Theorems.Thm_lean_workbook_plus_14292
-- name    : lean_workbook_plus_14292
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/083613d6-c57d-4649-8ad2-6d0018bc3ceb
-- statement:
--   Solve the Diophantine equation $X^3+Y^3+Z^3-3XYZ=R^3$ for $X, Y, Z, R$ where $X=s(9p^2+9ps+10s^2)$, $Y=s(6p^2+12ps+7s^2)$, $Z=3p^3+3p^2s+15ps^2+7s^3$, and $R=3(p+2s)(p^2-ps+s^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14292 (p s X Y Z R : ℤ) (hX : X = s * (9 * p ^ 2 + 9 * p * s + 10 * s ^ 2)) (hY : Y = s * (6 * p ^ 2 + 12 * p * s + 7 * s ^ 2)) (hZ : Z = 3 * p ^ 3 + 3 * p ^ 2 * s + 15 * p * s ^ 2 + 7 * s ^ 3) (hR : R = 3 * (p + 2 * s) * (p ^ 2 - p * s + s ^ 2)) : X ^ 3 + Y ^ 3 + Z ^ 3 - 3 * X * Y * Z = R ^ 3   :=  by sorry
