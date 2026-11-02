-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:52:31.741055+00:00
-- url     : https://prove2.me/theorems/a3a0b559-5297-496f-932d-5e752a281600
-- title:
--   Lower bound for maximal drawable graphs
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has at least 3|V|−6 edges. The proof route is to show maximality forces every face of a planar embedding to be triangular, then apply Euler’s formula. This isolates the maximality argument from the general planar upper bound; formalizing the face and augmentation arguments is the remaining core work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (dL : DecidableRel L.Adj) (hL : HasPlanarDrawingOn L) (hcard : 3 <= Fintype.card V) (hmax : forall (M : SimpleGraph V) (dM : DecidableRel M.Adj), L <= M -> HasPlanarDrawingOn M -> M <= L) : 3 * Fintype.card V <= L.edgeFinset.card + 6 := by sorry
