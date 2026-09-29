-- Prove2me | Theorems.Thm_lean_workbook_plus_80237
-- name    : lean_workbook_plus_80237
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/8bc055d8-f071-4e92-a5c5-56eab995c49f
-- statement:
--   We have \n\n $\begin{array}{l}\sum {{a^2}{b^2}} + \sum {{a^3}} \ge 2\sum {{a^2}} \Leftrightarrow 3\sum {{a^2}{b^2}} + 3\sum {{a^3}} \ge 6\sum {{a^2}} \\\Leftrightarrow 3\left( {{a^2}{b^2} + {b^2}{c^2} + {c^2}{a^2}} \right) + \left( {a + b + c} \right)\left( {{a^3} + {b^3} + {c^3}} \right) \ge \frac{2}{3}\left( {{a^2} + {b^2} + {c^2}} \right){\left( {a + b + c} \right)^2}\\\Leftrightarrow 3\sum {{a^2}{b^2}} + \sum {{a^4}} + \sum {a\left( {{b^3} + {c^3}} \right)} \ge \frac{2}{3}\left( {{a^2} + {b^2} + {c^2}} \right)\left( {{a^2} + {b^2} + {c^2} + 2ab + 2bc + 2ca} \right)\\\Leftrightarrow 3\sum {{a^2}{b^2}} + \sum {{a^4}} + \sum {a\left( {{b^3} + {c^3}} \right)} \ge \frac{2}{3}\left[ {\sum {{a^4}} + 2\sum {{a^2}{b^2}} + 2\sum {{a^3}\left( {b + c} \right)} + 2abc\left( {a + b + c} \right)} \right]\\\Leftrightarrow 9\sum {{a^2}{b^2}} + 3\sum {{a^4}} + 3\sum {a\left( {{b^3} + {c^3}} \right)} \ge 2\sum {{a^4}} + 4\sum {{a^2}{b^2}} + 4\sum {{a^3}\left( {b + c} \right)} + 4abc\left( {a + b + c} \right)\\\Leftrightarrow 5\sum {{a^2}{b^2}} + \sum {{a^4}} \ge \sum {{a^3}\left( {b + c} \right)} + 12abc\\\Leftrightarrow 5\sum {{a^2}{b^2}} + \left[ {\sum {{a^4}} + abc\left( {a + b + c} \right)} \right] \ge \sum {{a^3}\left( {b + c} \right)} + 15abc\end{array}$ It's true by $5\sum {{a^2}{b^2}} \ge 5abc\left( {a + b + c} \right) = 15abc,\,\,\sum {{a^4}} + abc\left( {a + b + c} \right) \ge \sum {{a^3}\left( {b + c} \right)} $ . Done!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80237 :
  ∀ a b c : ℝ, 3 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + (a + b + c) * (a^3 + b^3 + c^3) ≥
    2 / 3 * (a^2 + b^2 + c^2) * (a + b + c)^2   :=  by sorry
