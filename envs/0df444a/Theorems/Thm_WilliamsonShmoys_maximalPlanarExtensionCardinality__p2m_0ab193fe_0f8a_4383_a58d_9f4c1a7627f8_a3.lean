-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarExtensionCardinality__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
-- name    : WilliamsonShmoys.maximalPlanarExtensionCardinality__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:53:11.388816+00:00
-- url     : https://prove2.me/theorems/fdcf6722-88f2-45ca-bb18-4e42aed9226b
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The proof must show that maximality forces connectedness and triangular faces, then apply Euler’s formula and count face-edge incidences. The hypothesis includes the three-vertex boundary, where the maximal graph is a triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarExtensionCardinality__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N →
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       M.edgeFinset ⊆ N.edgeFinset) →
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       N.edgeFinset ⊆ M.edgeFinset))
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel M.Adj := dM
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
