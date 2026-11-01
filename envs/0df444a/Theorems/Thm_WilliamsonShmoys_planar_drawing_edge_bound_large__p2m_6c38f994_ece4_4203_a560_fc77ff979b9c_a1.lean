-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_large__p2m_6c38f994_ece4_4203_a560_fc77ff979b9c_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_large__p2m_6c38f994_ece4_4203_a560_fc77ff979b9c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:21.657144+00:00
-- url     : https://prove2.me/theorems/faf1e34b-c334-4cdd-9a5b-1160c97cacbd
-- title:
--   Euler edge bound for planar drawings with at least three vertices
-- statement:
--   A graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges. This is the large-cardinality conjunct of the target, isolated so its Euler and component-counting argument is reusable. A proof route is to establish the Euler bound for each connected planar component, handle components of size one or two directly, and sum the resulting bounds. The central remaining work is deriving the component bounds from the continuous-arc drawing predicate and formalizing the finite component accounting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_edge_bound_large__p2m_6c38f994_ece4_4203_a560_fc77ff979b9c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    3 ≤ Fintype.card V →
      6 + M.edgeSet.ncard ≤ 3 * Fintype.card V := by sorry
