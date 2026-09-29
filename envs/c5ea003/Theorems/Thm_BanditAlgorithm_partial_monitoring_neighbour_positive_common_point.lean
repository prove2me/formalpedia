-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_positive_common_point
-- name    : BanditAlgorithm.partial_monitoring_neighbour_positive_common_point
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:32:22.147275+00:00
-- url     : https://prove2.me/theorems/2aa3080f-65d7-4b7a-8d9e-b97b4e9611b1
-- title:
--   A neighbouring common cell contains a strictly positive distribution
-- statement:
--   Let $a,b$ be neighbouring actions in a finite partial-monitoring game. Their common cell contains an outcome distribution in the relative interior of the probability simplex: there is $u\in C_a\cap C_b$ such that
--
--   $$
--   u_i>0\qquad\text{for every outcome }i.
--   $$
--
--   This supplies the interior base environment used for the two alternatives $u\pm\Delta q$. The strict coordinate inequalities ensure both perturbations remain probability distributions when $\Delta$ is sufficiently small.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12, Step 1, printed pp. 488–490. The proof chooses the centroid of C_a ∩ C_b and states on p. 490 that it is not on the boundary of the probability simplex, so every coordinate is positive.

import Definitions.Def_PartialMonitoringGame

theorem BanditAlgorithm.partial_monitoring_neighbour_positive_common_point
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (a b : Fin k) (hab : NeighbouringActions G a b) :
    ∃ u ∈ pmCell G a ∩ pmCell G b, ∀ i : Fin d, 0 < u i := by sorry
