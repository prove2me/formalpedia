-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_completion_exact_edge_count__p2m_e9f7baec_2042_4774_99e6_a1421ec04a69_a1
-- name    : WilliamsonShmoys.exists_planar_completion_exact_edge_count__p2m_e9f7baec_2042_4774_99e6_a1421ec04a69_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:23:14.315355+00:00
-- url     : https://prove2.me/theorems/92669c9b-dd39-4b0e-bff1-b3f1c8b950b1
-- title:
--   Planar completion with an exact edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_completion_exact_edge_count__p2m_e9f7baec_2042_4774_99e6_a1421ec04a69_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  sorry
