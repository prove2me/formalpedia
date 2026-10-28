-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:03:06.884956+00:00
-- url     : https://prove2.me/theorems/a4f8be7d-b962-4956-94dc-92988cb44750
-- title:
--   Planar edge bound from an arc drawing
-- statement:
--   Any graph on at least three vertices with the supplied crossing-free arc drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
