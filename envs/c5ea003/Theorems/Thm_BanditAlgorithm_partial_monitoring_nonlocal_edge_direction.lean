-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_nonlocal_edge_direction
-- name    : BanditAlgorithm.partial_monitoring_nonlocal_edge_direction
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:20:17.680869+00:00
-- url     : https://prove2.me/theorems/8fc2c65d-f3af-447a-b6bd-f608b6fdb5ae
-- title:
--   A nonlocally observable edge admits an indistinguishable perturbation direction
-- statement:
--   Fix neighbouring actions $a,b$ in a finite partial-monitoring game, and suppose their loss difference has no estimator supported on the neighbourhood $N_{ab}$. Then there is a direction $q\in\mathbb R^d$ satisfying
--
--   $$
--   \sum_i q_i=0,\qquad \langle \ell_a-\ell_b,q\rangle=1,
--   $$
--
--   and, for every $c\in N_{ab}$ and every feedback symbol $\sigma$,
--
--   $$
--   \sum_{i:\,\Phi_{ci}=\sigma}q_i=0.
--   $$
--
--   Thus the perturbations $u\pm\Delta q$ preserve total probability and induce identical feedback distributions for every action in $N_{ab}$, while separating the expected losses of $a$ and $b$ at unit rate.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12, Step 1, printed pp. 489–490, Eq. (37.6) and the construction immediately following it.

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

theorem BanditAlgorithm.partial_monitoring_nonlocal_edge_direction
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : NeighbouringActions G a b)
    (hnlocal : ¬ ∃ f : Fin k × 𝕊 → ℝ, IsLocalLossEstimator G a b f) :
    ∃ q : Fin d → ℝ,
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ c : Fin k, c ∈ pmNeighbourhood G a b → ∀ σ : 𝕊,
        (∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i) = 0 := by sorry
