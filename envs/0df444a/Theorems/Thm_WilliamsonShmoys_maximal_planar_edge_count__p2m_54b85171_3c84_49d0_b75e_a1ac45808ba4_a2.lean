-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:47.844644+00:00
-- url     : https://prove2.me/theorems/8b804cdd-68ca-48da-bde7-dd4a5c81f51a
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal planar simple graph on at least three vertices has 3|V|−6 edges. This supplies the counting step in the parent. A proof route is to establish connectedness and triangular faces from maximality, then use the planar Euler formula and count edge-face incidences; the main remaining work is formalizing those embedding and face-count arguments for the given crossing-free arc predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → N ≤ K → K = N)
    (hcard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
