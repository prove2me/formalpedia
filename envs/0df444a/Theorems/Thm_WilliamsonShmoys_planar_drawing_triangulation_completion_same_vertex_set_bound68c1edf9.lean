-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_same_vertex_set_bound68c1edf9
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_same_vertex_set_bound68c1edf9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T07:03:55.639304+00:00
-- url     : https://prove2.me/theorems/437ae037-6315-4598-a71b-f3c87f44dd3b
-- title:
--   Triangulation completion for a planar edge bound
-- statement:
--   Any finite simple graph with the supplied crossing-free drawing and at least three vertices can be extended on the same vertex set, retaining all original edges, to a drawn graph with exactly 3|V|−6 edges. This child contains the completion and Euler-count argument; the parent needs only edge inclusion and arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_same_vertex_set_bound68c1edf9
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      L.edgeSet ⊆ H.edgeSet /\
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
