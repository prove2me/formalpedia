-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound__p2m_3948e52b_b0d7_479f_b947_2a84e2ebda9e_a1
-- name    : WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_3948e52b_b0d7_479f_b947_2a84e2ebda9e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:02:22.713081+00:00
-- url     : https://prove2.me/theorems/2a90ede6-b2ad-40d4-a25e-8e3e873838ed
-- title:
--   Simple edge bound for a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges. This isolates the incidence argument’s planar-topology burden; combined with the target’s Euler equation, it yields the desired inequality. The boundary case of exactly three vertices satisfies the same bound. A proof can pass from the arc drawing to a planar embedding, augment to a maximal planar graph without adding vertices, and use Euler’s formula together with the minimum three edge occurrences on each face boundary. Formalizing that passage and augmentation for this drawing definition is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_3948e52b_b0d7_479f_b947_2a84e2ebda9e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
