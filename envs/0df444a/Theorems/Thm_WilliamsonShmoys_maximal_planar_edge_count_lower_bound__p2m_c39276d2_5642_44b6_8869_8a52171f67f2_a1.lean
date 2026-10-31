-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:25.058568+00:00
-- url     : https://prove2.me/theorems/efbdf66e-6b79-4361-98ec-bc960d2ecfa5
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has at least 3|V| − 6 edges. The proof route is to derive connected triangular face data from maximality, then use Euler's formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
