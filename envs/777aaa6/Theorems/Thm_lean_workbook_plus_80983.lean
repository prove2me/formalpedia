-- Prove2me | Theorems.Thm_lean_workbook_plus_80983
-- name    : lean_workbook_plus_80983
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/4ad32bf2-dddc-4dcc-acc7-20b4177e7615
-- statement:
--   Let the numbers be $A$ and $B$ . Let $g$ denote the GcF of $A$ and $B$ . Then let $A$ and $B$ equal $gx$ and $gy$ , respectively, where $x$ and $y$ are relatively prime integers. This means that the LcM of $A$ and $B$ is $gxy$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80983  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : Nat.gcd a b = g)
  (h₂ : Nat.lcm a b = l)
  (h₃ : 0 < g ∧ 0 < l)
  (h₄ : l = g * x * y)
  (h₅ : Nat.gcd x y = 1) :
  l = g * x * y   :=  by sorry
