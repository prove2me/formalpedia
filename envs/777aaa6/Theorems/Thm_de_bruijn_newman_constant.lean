-- Prove2me | Theorems.Thm_de_bruijn_newman_constant
-- name    : de_bruijn_newman_constant
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-31T20:43:54.20716+00:00
-- url     : https://prove2.me/theorems/8515e5ed-1ef2-4134-a7a6-9a5c22e15a51
-- statement:
--   The de Bruijn–Newman constant Λ: The Riemann Hypothesis is equivalent to Λ ≤ 0. It is known that 0 ≤ Λ (Rodgers–Tao 2018, proving Λ ≥ 0 refuted the conjecture that Λ < 0). Proving Λ = 0 would prove RH. The question whether Λ = 0 is equivalent to but distinct from RH.
-- source:
--   https://en.wikipedia.org/wiki/De_Bruijn%E2%80%93Newman_constant

import Mathlib

import Mathlib

theorem de_bruijn_newman_constant :
    ∃ (Lambda : ℝ),
      Lambda = 0 ∧
      ∀ (t : ℝ), t < Lambda →
        ∃ (z : ℂ), z.re > 0 ∧
          ∑' (n : ℕ), Complex.exp (-t * (n : ℂ)^2 * Real.pi) *
            (2 * Real.pi * (n : ℝ)^2 - 3) *
            Complex.exp (-(n : ℂ)^2 * Real.pi) = 0 := by
  sorry
