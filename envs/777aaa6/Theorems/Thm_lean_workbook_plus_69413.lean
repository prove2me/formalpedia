-- Prove2me | Theorems.Thm_lean_workbook_plus_69413
-- name    : lean_workbook_plus_69413
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a37ed27c-6d3c-4463-a24b-1f7f4cd4b9f0
-- statement:
--   Factor the given numbers. For example, 80601=201*401.\n$\frac{10001 \cdot 20301 \cdot 80601 \cdot 180901}{101 \cdot 401 \cdot 601 \cdot 701} = \frac{10001 \cdot 201 \cdot 101 \cdot 201 \cdot 401 \cdot 301 \cdot 601}{101 \cdot 401 \cdot 601 \cdot 701} = \frac{10001 \cdot 201^2 \cdot 301}{701}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69413 :
  (10001 * 20301 * 80601 * 180901) / (101 * 401 * 601 * 701) = (10001 * 201^2 * 301) / 701   :=  by sorry
