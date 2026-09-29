-- Prove2me | Theorems.Thm_lean_workbook_plus_79949
-- name    : lean_workbook_plus_79949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/533a8141-223b-4cce-a9f5-10c8dff5c323
-- statement:
--   If $n=2^u-2^v+t$ where $u>v\ge 0$ and $t<2^{v-1}$ : \n $f(n)=2^v-t-1$ and $g(n)=f(f(n))=t$ \nSo $n-g(n)=2^u-2^v$ and $f(n-g(n))=2^v-1$ and $g(n-g(n))=f(2^v-1)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79949  (u v t : ℕ)
  (n : ℕ)
  (f g : ℕ → ℕ)
  (h₀ : n = 2^u - 2^v + t)
  (h₁ : u > v)
  (h₂ : v >= 0)
  (h₃ : t < 2^(v-1))
  (h₄ : f n = 2^v - t - 1)
  (h₅ : g n = f (f n))
  (h₆ : n - g n = 2^u - 2^v)
  (h₇ : f (n - g n) = 2^v - 1)
  (h₈ : g (n - g n) = f (2^v - 1))
  (h₉ : f (2^v - 1) = 0) :
  g n = t   :=  by sorry
