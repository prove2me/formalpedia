-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
-- name    : WilliamsonShmoys.planar_drawing_euler_data__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T01:55:55.374294+00:00
-- url     : https://prove2.me/theorems/4a6667dc-3f5b-4370-a682-d1aef720dceb
-- title:
--   Extract Euler face data from a planar drawing
-- statement:
--   A crossing-free drawing of a connected simple graph with at least three vertices yields finite face data satisfying Euler’s equation, with every face boundary having length at least three and total boundary length twice the edge count. Boundary lengths count edge-sides with multiplicity, including both sides of a bridge. This removes the drawing-to-Euler topology argument from the parent; a concrete proof route constructs the rotation system and face walks induced by the arcs, then applies planar topology to obtain Euler’s equation and the edge-side count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_PlanarEulerData__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_data__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hConn : G.Connected) (hCard : 3 <= Fintype.card V) : Nonempty (WilliamsonShmoys.PlanarEulerData__p2m_d55c87f4_5c3d_477a_90f7_18a99497d822_a5 G) := by sorry
