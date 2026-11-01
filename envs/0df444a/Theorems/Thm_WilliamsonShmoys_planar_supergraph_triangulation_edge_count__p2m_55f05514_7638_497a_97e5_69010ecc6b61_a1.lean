-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count__p2m_55f05514_7638_497a_97e5_69010ecc6b61_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_55f05514_7638_497a_97e5_69010ecc6b61_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:56:04.378038+00:00
-- url     : https://prove2.me/theorems/9fcd878d-5db4-4b13-99bb-56edaa5c5ac0
-- title:
--   Triangulated planar supergraph completion
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices has a crossing-free supergraph on the same vertex set whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_55f05514_7638_497a_97e5_69010ecc6b61_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
