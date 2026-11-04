-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_924b9ea4_0b38_4572_b493_5a5eee48f103_a2
-- name    : WilliamsonShmoys.planar_supergraph_triangulation__p2m_924b9ea4_0b38_4572_b493_5a5eee48f103_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:46:31.116258+00:00
-- url     : https://prove2.me/theorems/4b25ff07-58d5-4fd9-86ca-512a78018f09
-- title:
--   Extension of a finite planar drawing to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertex set with exactly 3n−6 edges. The hypothesis n ≥ 3 is needed for the triangulation and its edge count, including the n = 3 boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation__p2m_924b9ea4_0b38_4572_b493_5a5eee48f103_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    ∃ L : SimpleGraph V,
      K.edgeFinset ⊆ L.edgeFinset ∧
      HasPlanarDrawingOn L ∧
      L.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
