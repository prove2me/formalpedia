-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_maximal_planar_drawing_f3620a14
-- name    : WilliamsonShmoys.edge_count_eq_of_maximal_planar_drawing_f3620a14
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:25:33.633933+00:00
-- url     : https://prove2.me/theorems/7a8ede97-e530-4972-911e-c831433c7f7b
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable graph on at least three finite vertices that has no drawable proper supergraph on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_eq_of_maximal_planar_drawing_f3620a14
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R → S ≤ R → R ≤ S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
