-- Prove2me | Theorems.Thm_lean_workbook_plus_65921
-- name    : lean_workbook_plus_65921
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e26011d0-5281-4c7c-9bca-fbf904707e60
-- statement:
--   If we join every other point of the 12-gon, we get a regular hexagon, Since a regular hexagon is made up of six equilateral triangles we know that $ A_6A_8=6$ . We also Know that the height of the equilateral triangle is $ 6\sin 60 = 3\sqrt{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65921 :
  6 * Real.sin (60 * Real.pi / 180) = 3 * Real.sqrt 3   :=  by sorry
