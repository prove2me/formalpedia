-- Prove2me | Theorems.Thm_lean_workbook_plus_53634
-- name    : lean_workbook_plus_53634
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/444f5c07-41ad-404c-8bbe-a159678a99cd
-- statement:
--   The following inequality is equivalent to \n\n $ 3R^2 - \frac {s^4 - 8Rrs^2 + 2r^2s^2 + 16R^2r^2 + 8Rr^3 + r^4}{2(s^2 - 4Rr - r^2)}\geq 0$ \n\n $ \Longleftrightarrow - s^4 + (6R^2 + 8Rr - 2r^2)s^2 - 24R^3r - 22R^2r^2 - r^4 - 8Rr^3\geq 0$ \n\n $ \Longleftrightarrow - s^4 + (4R^2 + 20Rr - 2r^2)s^2 - r(4R + r)^3 + 2R((R - 6r)s^2 + r(4R + r)(2r + 5R))\geq 0$ \n\n can prove $ - s^4 + (4R^2 + 20Rr - 2r^2)s^2 - r(4R + r)^3\geq 0$ \n\n and \n\n $ (R - 6r)s^2 + r(4R + r)(2r + 5R)\geq - 4rs^2 + r(4R + r)(2r + 5R)$ \n\n $ = r( - 4s^2 + (4R + r)(2r + 5R))\geq r( - 4(4R^2 + 4Rr + 3r^2) + (4R + r)(2r + 5R))$ \n\n $ = r(5r + 4R)(R - 2r)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53634 :
  ∀ (R r s : ℝ), 3 * R^2 - (s^4 - 8 * R * r * s^2 + 2 * r^2 * s^2 + 16 * R^2 * r^2 + 8 * R * r^3 + r^4) / (2 * (s^2 - 4 * R * r - r^2)) ≥ 0   :=  by sorry
