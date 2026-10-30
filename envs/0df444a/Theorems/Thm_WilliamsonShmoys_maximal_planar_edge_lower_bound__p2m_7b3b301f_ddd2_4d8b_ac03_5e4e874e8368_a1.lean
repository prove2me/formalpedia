-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:48.230754+00:00
-- url     : https://prove2.me/theorems/4a9048a5-f8b9-492a-9599-928b8a8a35af
-- title:
--   Maximal planar graphs attain the Euler bound
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable graphs on the same vertex set has at least 3|V| − 6 edges. The proof route is to show maximality forces a triangulation, then use Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
