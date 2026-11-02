-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_completion__p2m_76432751_4a60_438b_af25_c322d55d602e_a2
-- name    : WilliamsonShmoys.planar_supergraph_maximal_completion__p2m_76432751_4a60_438b_af25_c322d55d602e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:09:41.375094+00:00
-- url     : https://prove2.me/theorems/0e267cb6-c5af-47f0-9958-0b72bfd3b3ee
-- title:
--   Maximal planar supergraph completion on a fixed vertex set
-- statement:
--   Every finite planar simple graph with at least three vertices has a planar supergraph on the same vertex set that is inclusion-maximal among planar supergraphs on that set. Finiteness allows choosing a planar supergraph with a largest edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_completion__p2m_76432751_4a60_438b_af25_c322d55d602e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       G.edgeFinset ⊆ H.edgeFinset ∧
       WilliamsonShmoys.HasPlanarDrawingOn H ∧
       ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
         letI : DecidableRel K.Adj := dK
         WilliamsonShmoys.HasPlanarDrawingOn K →
         H.edgeFinset ⊆ K.edgeFinset → K.edgeFinset ⊆ H.edgeFinset) := by sorry
