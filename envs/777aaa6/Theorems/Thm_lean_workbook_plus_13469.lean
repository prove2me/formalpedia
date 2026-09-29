-- Prove2me | Theorems.Thm_lean_workbook_plus_13469
-- name    : lean_workbook_plus_13469
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f271f6a5-16c6-4f90-9b29-d43457504746
-- statement:
--   Let $f_0$ be the probability that F wins, starting from the beginning of the game. Let $f_T$ be the probability that F wins, given that tails has just been thrown, and let $f_H$ and $f_{HH}$ be the probability that F wins, given that one or two heads have just been thrown, respectively. Then \n\begin{align*}f_0&=\tfrac12(f_T+f_H)\\f_T&=\tfrac12(1+f_H)\\f_H&=\tfrac12(f_T+f_{HH})\\f_{HH}&=\tfrac12(f_T+0)\\\end{align*} Thus by substitution $f_T=\tfrac12+\tfrac12(\tfrac12f_T+\tfrac14f_T)\implies \tfrac58f_T=\tfrac12$ from which we get $f_T=\tfrac45,\ f_H=\tfrac35\implies f_0=\tfrac7{10}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13469  (f₀ f₁ f₂ f₃ : ℚ)
  (h₀ : f₀ = (f₁ + f₂) / 2)
  (h₁ : f₁ = (1 + f₂) / 2)
  (h₂ : f₂ = (f₁ + f₃) / 2)
  (h₃ : f₃ = (f₁ + 0) / 2) :
  f₀ = 7 / 10   :=  by sorry
