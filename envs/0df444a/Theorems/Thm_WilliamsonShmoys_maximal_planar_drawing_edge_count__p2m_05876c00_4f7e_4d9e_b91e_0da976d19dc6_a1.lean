-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:05.153841+00:00
-- url     : https://prove2.me/theorems/55f05514-7638-497a-97e5-69010ecc6b61
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable finite simple graph with at least three vertices has exactly 3|V|−6 edges. The standard route proves that maximality forces a triangulation and then applies Euler’s formula and face-edge incidence counting. This is the remaining topological core of the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      ∀ u v, N.Adj u v → M.Adj u v) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
