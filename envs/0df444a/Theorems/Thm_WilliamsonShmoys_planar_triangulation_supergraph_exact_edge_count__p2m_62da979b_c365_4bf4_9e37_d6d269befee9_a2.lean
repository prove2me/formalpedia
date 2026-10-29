-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_62da979b_c365_4bf4_9e37_d6d269befee9_a2
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_62da979b_c365_4bf4_9e37_d6d269befee9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:10:28.950855+00:00
-- url     : https://prove2.me/theorems/d2b9de51-527b-4570-bab3-6317ebc95efe
-- title:
--   Drawable graph completion with the maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type that contains all its edges and has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_62da979b_c365_4bf4_9e37_d6d269befee9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
