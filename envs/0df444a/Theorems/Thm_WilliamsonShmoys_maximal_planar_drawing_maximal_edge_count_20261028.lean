-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_maximal_edge_count_20261028
-- name    : WilliamsonShmoys.maximal_planar_drawing_maximal_edge_count_20261028
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:16:27.240714+00:00
-- url     : https://prove2.me/theorems/8840e11a-ebd4-4831-bb33-80096d43ef91
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph has exactly 3|V|−6 edges. This supplies the geometric and counting step needed after maximal extension. A proof route is to obtain a plane embedding from the given drawing, show that any face with more than three boundary edges permits adding an edge inside that face, conclude every face is triangular, and combine the triangular face count with Euler’s formula. Check the three-vertex case explicitly in the argument. This is the remaining core obligation; the continuous-arc drawing definition makes deriving and formalizing the embedding and face facts substantial work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_maximal_edge_count_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
