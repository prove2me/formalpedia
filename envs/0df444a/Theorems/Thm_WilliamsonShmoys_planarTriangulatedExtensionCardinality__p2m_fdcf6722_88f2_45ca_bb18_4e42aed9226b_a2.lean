-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarTriangulatedExtensionCardinality__p2m_fdcf6722_88f2_45ca_bb18_4e42aed9226b_a2
-- name    : WilliamsonShmoys.planarTriangulatedExtensionCardinality__p2m_fdcf6722_88f2_45ca_bb18_4e42aed9226b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:09:35.675725+00:00
-- url     : https://prove2.me/theorems/26871514-c4d6-4964-8af5-28b3596c0479
-- title:
--   Planar extension with triangulated edge count
-- statement:
--   Any crossing-free drawing of a simple graph on a finite ordered vertex set with at least three vertices can be extended, without adding vertices, to a crossing-free drawing whose graph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarTriangulatedExtensionCardinality__p2m_fdcf6722_88f2_45ca_bb18_4e42aed9226b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N ∧
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       M.edgeFinset ⊆ N.edgeFinset) ∧
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       N.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
