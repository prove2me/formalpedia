-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_same_vertex_completion_edge_bound__p2m_c80d2f01_7a07_4cb5_848a_3ed178dc77f9_a1
-- name    : WilliamsonShmoys.planar_drawing_same_vertex_completion_edge_bound__p2m_c80d2f01_7a07_4cb5_848a_3ed178dc77f9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:38.383416+00:00
-- url     : https://prove2.me/theorems/c8531657-ec59-40f0-b6a5-b2e5a59fa2d0
-- title:
--   Same-vertex planar completion edge bound
-- statement:
--   Any planar drawing on at least three vertices can be extended, using the same vertex set, to a planar graph containing all original edges and having at least 3|V|−6 edges. This separates the geometric completion and Euler-count argument from the target’s maximality step. Its independent proof route is to add noncrossing edges to a finite maximal planar supergraph, then count its edges by Euler’s formula; the construction must preserve the drawing predicate and address disconnected graphs and isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_same_vertex_completion_edge_bound__p2m_c80d2f01_7a07_4cb5_848a_3ed178dc77f9_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) : letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj; ∃ T : SimpleGraph V, (∀ {u v : V}, H.Adj u v → T.Adj u v) ∧ HasPlanarDrawingOn T ∧ 3 * Fintype.card V - 6 ≤ T.edgeFinset.card := by sorry
