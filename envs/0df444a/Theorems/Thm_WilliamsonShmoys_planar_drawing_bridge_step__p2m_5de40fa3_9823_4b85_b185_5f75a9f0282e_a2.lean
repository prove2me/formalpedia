-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
-- name    : WilliamsonShmoys.planar_drawing_bridge_step__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:09:59.722641+00:00
-- url     : https://prove2.me/theorems/806ab279-09f1-47fe-9b7f-fe9caced9bd3
-- title:
--   Planar bridge extension across an edge-free cut
-- statement:
--   If a drawable finite graph has a nontrivial vertex cut with no edges crossing it, it has a drawable supergraph on the same vertices containing an edge across the cut.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_bridge_step__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (A : Set V) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hno : ∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v, u ∈ A ∧ v ∉ A ∧ H.Adj u v := by sorry
