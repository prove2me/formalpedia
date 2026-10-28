-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_edgeSet_ncard_mono
-- name    : WilliamsonShmoys.planar_simple_edge_bound_edgeSet_ncard_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:58:25.947025+00:00
-- url     : https://prove2.me/theorems/d6773988-c836-4ae2-8055-a363628555bc
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite V, graph inclusion implies inclusion of edge sets and hence monotonicity of their finite cardinalities. Prove using edge-set membership from G ≤ H and monotonicity of ncard.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_edge_bound_edgeSet_ncard_mono
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
