-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
-- name    : WilliamsonShmoys.simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:14:48.044618+00:00
-- url     : https://prove2.me/theorems/287d45f7-8fd6-4d69-bf9c-a1b2fb389f0f
-- title:
--   Drawable simple graphs have at most 3|V| - 6 edges
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V| - 6 edges. This isolates the planar Euler argument, which is the remaining core obligation. The condition |V| >= 3 is essential; at |V| = 3 the triangle attains equality. A proof route is to turn the drawing into a plane embedding, connect components if needed, extend to a maximal planar graph without adding vertices, and count triangular face-edge incidences using Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.simple_planar_edge_upper_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
