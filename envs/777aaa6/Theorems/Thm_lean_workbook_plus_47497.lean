-- Prove2me | Theorems.Thm_lean_workbook_plus_47497
-- name    : lean_workbook_plus_47497
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/54958a30-34cc-4662-9dbe-0fb1d22cc2cb
-- statement:
--   Given that\n $ x+y+z = 6$\n $ xy+yz+zx = 11$\n $ xyz = 6$ , then find $ x^5+y^5+z^5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47497 (x y z : ℝ) (h₁ : x + y + z = 6) (h₂ : x*y + y*z + z*x = 11) (h₃ : x*y*z = 6) : x^5 + y^5 + z^5 = 276   :=  by sorry
