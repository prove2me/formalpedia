-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_of_arcs
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_of_arcs
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:51:07.906798+00:00
-- url     : https://prove2.me/theorems/60f367cc-66c5-4f7a-984d-4a161a09ce98
-- title:
--   Edge count of an edge-maximal graph with an arc drawing
-- statement:
--   An edge-maximal graph satisfying the supplied crossing-free arc drawing definition, on at least three vertices, has exactly 3|V| − 6 edges. This is the remaining core mathematical obligation. A proof route is to show maximality forces each face of the planar embedding to be triangular, then count incidences between faces and edges and apply Euler’s formula. The condition |V| ≥ 3 is essential for the formula; it includes the three-vertex boundary case, where the maximal graph is K₃. The source declaration or proof was unavailable for verification, so this remains a proof obligation rather than an established result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_of_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
