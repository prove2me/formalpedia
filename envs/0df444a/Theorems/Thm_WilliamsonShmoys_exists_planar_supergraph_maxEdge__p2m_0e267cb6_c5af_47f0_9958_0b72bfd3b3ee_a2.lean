-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maxEdge__p2m_0e267cb6_c5af_47f0_9958_0b72bfd3b3ee_a2
-- name    : WilliamsonShmoys.exists_planar_supergraph_maxEdge__p2m_0e267cb6_c5af_47f0_9958_0b72bfd3b3ee_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:08.361188+00:00
-- url     : https://prove2.me/theorems/4b7bcbbd-d5fa-4530-8a50-f904d8174af1
-- title:
--   Planar supergraph with maximum edge count
-- statement:
--   Among planar graphs on the same finite vertex set that contain G, there is one whose edge set has maximum cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_maxEdge__p2m_0e267cb6_c5af_47f0_9958_0b72bfd3b3ee_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       G.edgeFinset ⊆ H.edgeFinset ∧
       WilliamsonShmoys.HasPlanarDrawingOn H ∧
       ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
         letI : DecidableRel K.Adj := dK
         WilliamsonShmoys.HasPlanarDrawingOn K →
         H.edgeFinset ⊆ K.edgeFinset →
         K.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
