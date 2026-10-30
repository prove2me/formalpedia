-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:04.785154+00:00
-- url     : https://prove2.me/theorems/82e54da5-16cf-4d16-b293-9f40ba57f2f4
-- title:
--   Maximal planar edge-count lower bound
-- statement:
--   A graph with a drawing on at least three vertices that has no drawable strict supergraph on the same vertex type has at least 3|V|−6 edges. Combined with the planar upper bound, this yields the target equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_ccd23c49_4232_4eaf_832f_2977e75f86e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N ≤ M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
