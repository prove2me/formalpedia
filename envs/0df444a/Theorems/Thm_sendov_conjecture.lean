-- Prove2me | Theorems.Thm_sendov_conjecture
-- name    : sendov_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:40:38.10625+00:00
-- url     : https://prove2.me/theorems/27ee96f0-b474-419f-89d9-fbac73b08df2
-- statement:
--   Sendov conjecture (Ilieff-Sendov 1958): If all roots of a complex polynomial of degree >= 2 lie in the closed unit disk, then for each root z0 there exists a critical point within distance 1 from z0. Proved for degree <= 8 and for large degree (Tao 2020).
-- source:
--   https://en.wikipedia.org/wiki/Sendov%27s_conjecture

import Mathlib

import Mathlib

theorem sendov_conjecture (p : Polynomial ℂ) (hdeg : 2 ≤ p.natDegree)
    (hroots : ∀ z : ℂ, p.IsRoot z → ‖z‖ ≤ 1)
    (z₀ : ℂ) (hz₀ : p.IsRoot z₀) :
    ∃ w : ℂ, p.derivative.IsRoot w ∧ ‖w - z₀‖ ≤ 1 := by
  sorry
