-- Prove2me | Theorems.Thm_lean_workbook_plus_48646
-- name    : lean_workbook_plus_48646
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/1e940bb5-f624-44c3-b4e1-c2bd133f2f22
-- statement:
--   Let the speed of the train be $v$ .\nLet the distance be $d$ .\nLet the original time be $t$ .\nIf the train hadn't broken down, then $vt=d$ ...........(1)\nBut when the train suffers a breakdown.\nThen\n $t'=t+3$\nSo, $\frac{3}{2}v+\frac{4}{5}v(t+1)=d$ ...........(2) (Because for the first 1.5 hrs it travels with speed $v$ , then 0.5 hrs for repairs, this gives $t+3-1.5-0.5=t+1$ hrs in which it travels at speed $\frac{4v}{5}$ ).\n\nCombining equation (1) and (2) and solving, we get\n $\frac{d}{v}=\frac{23}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48646  (v d t : ℝ)
  (h₀ : 0 < v ∧ 0 < d ∧ 0 < t)
  (h₁ : v * t = d)
  (h₂ : 3 / 2 * v + 4 / 5 * v * (t + 1) = d) :
  d / v = 23 / 2   :=  by sorry
