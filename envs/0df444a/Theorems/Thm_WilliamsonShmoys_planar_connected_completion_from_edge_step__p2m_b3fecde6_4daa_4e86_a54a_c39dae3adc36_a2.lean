-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_completion_from_edge_step__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
-- name    : WilliamsonShmoys.planar_connected_completion_from_edge_step__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:21.422203+00:00
-- url     : https://prove2.me/theorems/3c563abc-0f35-48b3-b23d-cb0a46677442
-- title:
--   Complete a finite graph by repeated bridge insertions
-- statement:
--   For a finite vertex type, if every disconnected graph satisfying P can be extended to a graph satisfying P by adding an edge across two of its components, then every starting graph satisfying P has a connected supergraph satisfying P. A proof route is to choose a P-supergraph of H with maximal edge count among the finitely many simple graphs on V. The step hypothesis contradicts maximality if that graph is disconnected. The lemma handles an already-connected H by allowing the maximal choice to be H itself.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_completion_from_edge_step__p2m_b3fecde6_4daa_4e86_a54a_c39dae3adc36_a2
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V) (hP : P H)
    (step : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ P K ∧ ∃ u v, ¬ G.Reachable u v ∧ K.Adj u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ P K := by sorry
