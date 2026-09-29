-- Prove2me | Theorems.Thm_BanditAlgorithm_pmPsi_le_quadratic
-- name    : BanditAlgorithm.pmPsi_le_quadratic
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:40:38.120737+00:00
-- url     : https://prove2.me/theorems/489b4c34-4e47-47ad-a394-65bb7cf1c6f3
-- title:
--   Quadratic upper bound for the Algorithm 26 stability function
-- statement:
--   Let q be a probability distribution on a finite action set and let z be a real vector with z_b at least -1 in every coordinate. For the exponential-weights stability function
--
--   $$
--   \Psi_q(z)=\sum_b q_b\bigl(e^{-z_b}+z_b-1\bigr),
--   $$
--
--   one has the quadratic bound
--
--   $$
--   \Psi_q(z)\leq\sum_b q_b z_b^2.
--   $$
--
--   This is the pointwise stability estimate used in both the global- and local-observability analyses of Algorithm 26.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, equation (37.15), printed p. 497, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

namespace BanditAlgorithm

/-! Lattimore--Szepesvári, equation (37.15), printed p. 497. -/

theorem pmPsi_le_quadratic {k : ℕ} (q z : Fin k → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin k)) (hz : ∀ b, -1 ≤ z b) :
    pmPsi q z ≤ ∑ b : Fin k, q b * (z b) ^ 2 := by
  sorry

end BanditAlgorithm
