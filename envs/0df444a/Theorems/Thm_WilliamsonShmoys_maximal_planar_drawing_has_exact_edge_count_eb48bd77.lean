-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count_eb48bd77
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_eb48bd77
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:47:21.97151+00:00
-- url     : https://prove2.me/theorems/1b1036c5-3c27-4dd8-b114-1401cd3dc974
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite vertices that has no drawable proper supergraph has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_eb48bd77
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet → ¬ HasPlanarDrawingOn M) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
