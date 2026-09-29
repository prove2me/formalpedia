-- Prove2me | Theorems.Thm_lean_workbook_plus_3052
-- name    : lean_workbook_plus_3052
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/29d0eb12-67ae-42b2-8d5e-b4249e20b783
-- statement:
--   And since $u_1+u_2=v_1+v_2=w_1+w_2=t_1+t_2$ and $u_1+u_2+v_1+v_2+w_1+w_2+t_1+t_2=36$ , we get $u_1+u_2=v_1+v_2=w_1+w_2=t_1+t_2=9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3052  (u v w t : ℕ → ℕ)
  (h₀ : u 1 + u 2 = v 1 + v 2)
  (h₁ : v 1 + v 2 = w 1 + w 2)
  (h₂ : w 1 + w 2 = t 1 + t 2)
  (h₃ : u 1 + u 2 + v 1 + v 2 + w 1 + w 2 + t 1 + t 2 = 36) :
  u 1 + u 2 = 9 ∧ v 1 + v 2 = 9 ∧ w 1 + w 2 = 9 ∧ t 1 + t 2 = 9   :=  by sorry
