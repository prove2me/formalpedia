-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_has_maximal_extension__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
-- name    : WilliamsonShmoys.planar_drawable_supergraph_has_maximal_extension__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:05.291548+00:00
-- url     : https://prove2.me/theorems/456d6f91-af0e-46c2-8bb6-0425e8955342
-- title:
--   A drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph has an inclusion-maximal drawable supergraph on the same vertices. This isolates finite edge-set maximization from the planar counting argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_supergraph_has_maximal_extension__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      letI : DecidableRel G.Adj := dG
      letI : DecidableRel H.Adj := dH
      HasPlanarDrawingOn H ∧
      G.edgeFinset ⊆ H.edgeFinset ∧
      ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        letI : DecidableRel H.Adj := dH
        letI : DecidableRel K.Adj := dK
        HasPlanarDrawingOn K →
        H.edgeFinset ⊆ K.edgeFinset →
        K.edgeFinset = H.edgeFinset := by sorry
