-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_d2b9de51_527b_4570_bab3_6317ebc95efe_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_d2b9de51_527b_4570_bab3_6317ebc95efe_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:24:36.96749+00:00
-- url     : https://prove2.me/theorems/e094cc24-53fc-49c4-8e51-8d82cdfe65a0
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable finite simple graph with at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_d2b9de51_527b_4570_bab3_6317ebc95efe_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V,
      N.edgeSet ⊆ P.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      P.edgeSet = N.edgeSet) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
