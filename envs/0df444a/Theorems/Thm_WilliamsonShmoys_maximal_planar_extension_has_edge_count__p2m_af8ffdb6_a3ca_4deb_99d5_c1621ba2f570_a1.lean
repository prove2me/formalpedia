-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_has_edge_count__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_has_edge_count__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:35:42.673963+00:00
-- url     : https://prove2.me/theorems/b5935805-1780-4fdc-8b62-9214cd276435
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The proof route is to use maximality to establish connectedness and triangular faces in a planar embedding, then combine the face-degree sum with Euler’s formula. The case of three vertices is included: maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_has_edge_count__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
      3 * Fintype.card V = M.edgeFinset.card + 6) := by sorry
