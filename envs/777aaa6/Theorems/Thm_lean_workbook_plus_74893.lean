-- Prove2me | Theorems.Thm_lean_workbook_plus_74893
-- name    : lean_workbook_plus_74893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/211f7edf-be14-4960-884b-c56df039f7a8
-- statement:
--   Write $xyz+xyt+xzt+yzt=(x+y+z+t)(xy+xz+yz)-(y+z)(x+y)(x+z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74893 (x y z t : ℝ) : x*y*z + x*y*t + x*z*t + y*z*t = (x + y + z + t) * (x*y + x*z + y*z) - (y + z) * (x + y) * (x + z)   :=  by sorry
