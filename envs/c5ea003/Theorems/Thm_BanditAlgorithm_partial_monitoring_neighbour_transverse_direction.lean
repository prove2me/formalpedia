-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_transverse_direction
-- name    : BanditAlgorithm.partial_monitoring_neighbour_transverse_direction
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T16:48:27.459622+00:00
-- url     : https://prove2.me/theorems/cf18ab63-afed-44a9-8018-77d7000993a5
-- title:
--   A neighbouring cell pair has a normalized transverse direction
-- statement:
--   For every neighbouring pair of actions $a,b$ in a finite partial-monitoring game, there is a tangent direction $q$ to the outcome simplex such that
--
--   $$
--   \sum_i q_i=0,\qquad \langle L_a-L_b,q\rangle=1.
--   $$
--
--   The zero-sum condition preserves total probability under small perturbations, while the normalization makes the relative loss of the two actions change at unit speed. This is the elementary transverse direction used in two-environment lower bounds.
--
--   **Formalization Note** Neighbourhood excludes duplicate loss rows: otherwise the two equal cells would have to have both codimension zero and codimension one. Orthogonal projection away from the constant-vector subspace then constructs $q$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 37.14 proof sketch, printed p. 492 (PDF p. 500), transverse perturbations around a neighbouring cell face; https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set

theorem BanditAlgorithm.partial_monitoring_neighbour_transverse_direction
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : NeighbouringActions G a b) :
    ∃ q : Fin d → ℝ,
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 := by
  sorry
