-- Prove2me | Theorems.Thm_lean_workbook_plus_17920
-- name    : lean_workbook_plus_17920
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/706d0e17-3c6d-4f49-af65-2d1703b002e4
-- statement:
--   Suppose $n^2+d=u^2$ while $2n^2=kd$ with $d,n,k,u\in\mathbb N$ \nNote that this implies $kn^2+2n^2=ku^2$ and so $(k+2)n^2=ku^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17920    (d n k u : ℕ)
    (h₁ : n^2 + d = u^2)
    (h₂ : 2 * n^2 = k * d) :
    k * n^2 + 2 * n^2 = k * u^2   :=  by sorry
