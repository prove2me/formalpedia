-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_from_bridge_steps__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_from_bridge_steps__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:10:05.591569+00:00
-- url     : https://prove2.me/theorems/be2db1e0-df49-4de2-8924-46bf2933b6cf
-- title:
--   Connected planar extension from bridge steps
-- statement:
--   For a finite graph with at least three vertices, if every drawable graph admits a planar bridge extension across each nontrivial edge-free cut, then the input graph has a connected planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_from_bridge_steps__p2m_5de40fa3_9823_4b85_b185_5f75a9f0282e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hbridge : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G →
      ∀ (A : Set V), A.Nonempty → Aᶜ.Nonempty →
        (∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v) →
        ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
          ∃ u v, u ∈ A ∧ v ∉ A ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected := by sorry
