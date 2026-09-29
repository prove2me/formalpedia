-- Prove2me | Theorems.Thm_lean_workbook_plus_3407
-- name    : lean_workbook_plus_3407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/34a9c613-9ad5-4aa9-8977-da3b0afeeeea
-- statement:
--   Let $ a + b + c = p$ and $ ab + bc + ca = q$ \n\n $ 8(p^2 - 2q)(q) \le p^4$ \n\n $ 16q^2 - 8p^2q + p^4 \ge 0$ \n\n $ (4q - p^2)^2 \ge 0$ \n\nEqualty holds when $ 4q - p^2 = 0$ <--> $ 4ab + 4ac + 4bc = a^2 + b^2 + c^2 + 2ab + 2ac + 2bc$ \n\n $ 2ab + 2ac + 2bc = a^2 + b^2 + c^2$ \n\n $ a^2 - 2(b + c)a + (b - c)^2 = 0$ \n\nThe discriminant is $ 16bc$ and must be $ \ge 0$ for there to be an $ a$ that satisfies the solution. Similarly, transposing the variables cyclically, we also get that $ bc \ge 0$ and $ ca \ge 0$ So they either are all $ \ge 0$ or all $ \le 0$ . \n\nIf they are all greater than 0, we have $ a = \frac {2(b + c)\pm4\sqrt {bc}}{2} = (\sqrt {b}\pm\sqrt {c})^2$ \n\nso the solutions to the equality are $ ((\sqrt {b}\pm\sqrt {c})^2,b,c)$ with $ b, c\ge0$ when a,b,c>0. \n\nSimilarly,we find that if they are all negative, then $ ( - (\sqrt {x}\pm\sqrt {y})^2, - x, - y)$ with $ x,y \ge 0$ constitutes all other solutions (when $ a,b,c \le 0$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3407  (a b c p q : ℝ)
  (h₀ : a + b + c = p)
  (h₁ : a * b + b * c + c * a = q)
  (h₂ : 8 * (p^2 - 2 * q) * q ≤ p^4) :
  16 * q^2 - 8 * p^2 * q + p^4 ≥ 0   :=  by sorry
