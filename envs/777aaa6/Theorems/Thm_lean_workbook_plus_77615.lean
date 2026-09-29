-- Prove2me | Theorems.Thm_lean_workbook_plus_77615
-- name    : lean_workbook_plus_77615
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8541e09a-2a34-4c26-bd19-b5ae139294bf
-- statement:
--   Claim. If $u+v+w=0$ , then $\cos(u)^2+\cos(v)^2+\cos(w)^2=1+2\cos(u) \cos(v) \cos(w)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77615 (u v w : ℂ) (h : u + v + w = 0) :
  Complex.cos u ^ 2 + Complex.cos v ^ 2 + Complex.cos w ^ 2 =
    1 + 2 * Complex.cos u * Complex.cos v * Complex.cos w   :=  by sorry
