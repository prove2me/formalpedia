-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:21:45.121464+00:00
-- url     : https://prove2.me/theorems/195faade-280b-4083-9c27-3702ef776b42
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Any drawable graph on at least three vertices has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. Its edge count is at least the original graph’s edge count. The proof adds drawable edges until no further planar supergraph is possible; edge-count monotonicity follows from inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_7e28d180_08cc_4953_8752_6b4f2973fe5d_a1 {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
      (∀ S : SimpleGraph V, R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S ≤ R) ∧
      Q.edgeSet.ncard ≤ R.edgeSet.ncard := by sorry
