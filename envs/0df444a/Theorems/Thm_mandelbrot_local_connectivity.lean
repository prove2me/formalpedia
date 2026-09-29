-- Prove2me | Theorems.Thm_mandelbrot_local_connectivity
-- name    : mandelbrot_local_connectivity
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:54:33.290182+00:00
-- url     : https://prove2.me/theorems/2a5f985a-178a-4f73-97d5-429e507251e8
-- statement:
--   The MLC conjecture: The Mandelbrot set M is locally connected. If true, implies the Mandelbrot set = closure of hyperbolic parameters and all Julia sets of parameters on ∂M are locally connected. Open since 1980; proved for finitely renormalizable parameters by Lyubich (1997).
-- source:
--   https://en.wikipedia.org/wiki/Mandelbrot_set

import Mathlib

import Mathlib

noncomputable def mandelbrotSet : Set ℂ :=
    {c : ℂ | ∀ n : ℕ, ‖((fun z => z ^ 2 + c)^[n] 0)‖ ≤ 2}

theorem mandelbrot_local_connectivity :
    ∀ c ∈ mandelbrotSet, ∀ U : Set ℂ, IsOpen U → c ∈ U →
      ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧ V ⊆ U ∧
        IsConnected (V ∩ mandelbrotSet) := by
  sorry
