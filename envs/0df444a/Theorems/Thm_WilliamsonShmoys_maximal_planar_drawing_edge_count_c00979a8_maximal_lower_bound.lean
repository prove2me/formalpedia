-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_c00979a8_maximal_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_maximal_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:07:46.978991+00:00
-- url     : https://prove2.me/theorems/1d810a4e-8d53-47c8-a185-c764ff48b208
-- title:
--   Lower edge bound from maximality
-- statement:
--   A graph on at least three vertices that is maximal among graphs with the supplied crossing-free arc drawing has at least 3|V|−6 edges. Maximality and the lower bound on the vertex count are needed to rule out faces that could be triangulated by adding an edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_maximal_lower_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
