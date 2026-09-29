-- Prove2me | Theorems.Thm_lean_workbook_plus_50346
-- name    : lean_workbook_plus_50346
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/93259808-7d26-4945-95c0-b766a802aec1
-- statement:
--   well, first of all i think its rearangment as well, but those can be done by am-gm in most cases:\n $\frac{a^3b+a^3c+ab^3+ac^3}{2}\ge2\cdot\sqrt[4]{a^8b^4c^4}=2a^2bc$\n\ndo that cyclic with $a,b,c$ and add them up u get the needed inequality
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50346 : ∀ a b c : ℝ, (a^3 * b + a^3 * c + b^3 * a + c^3 * a) / 2 ≥ 2 * a^2 * b * c   :=  by sorry
