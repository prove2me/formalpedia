-- Prove2me | Theorems.Thm_lean_workbook_plus_80546
-- name    : lean_workbook_plus_80546
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1fa81590-fde9-41da-83a9-a1ad3d22e368
-- statement:
--   If $ x+y+z=0$ then $ 2(x^5+y^5+z^5)=5xyz(x^2+y^2+z^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80546  (x y z : ℂ)
  (h₀ : x + y + z = 0) :
  2 * (x^5 + y^5 + z^5) = 5 * x * y * z * (x^2 + y^2 + z^2)   :=  by sorry
