-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:23:53.344779+00:00
-- url     : https://prove2.me/theorems/deae8f05-60d7-4f42-a724-dd855162dd44
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ K : SimpleGraph V,
      letI : DecidableRel K.Adj := Classical.decRel K.Adj
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeFinset.card ≤ K.edgeFinset.card ∧
      (∀ L : SimpleGraph V,
        letI : DecidableRel L.Adj := Classical.decRel L.Adj
        K ≤ L → HasPlanarDrawingOn L → L ≤ K) := by sorry
