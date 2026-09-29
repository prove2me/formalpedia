-- Prove2me | Theorems.Thm_lean_workbook_plus_43932
-- name    : lean_workbook_plus_43932
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/bd792064-bc8c-4d7b-b6c2-d4cdf40967dd
-- statement:
--   Well known result: $a=x+y+z\ge xy+yz+zx $ it is: $x^2+y^2+z^2\ge a^2-2a$ it suffices to prove $ \frac{a^2-2a+4}{a}\ge 2+\frac{a^2}{3(6+a)} $ which is easy.( $a\ge 3$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43932 :  ∀ a : ℝ, a >= 3 → (a^2 - 2 * a + 4) / a ≥ 2 + a^2 / (3 * (6 + a))   :=  by sorry
