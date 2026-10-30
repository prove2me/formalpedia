-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_counts__p2m_00de7451_7f58_447b_bbcb_462fc14bc6b9_a4
-- name    : WilliamsonShmoys.planar_drawing_euler_counts__p2m_00de7451_7f58_447b_bbcb_462fc14bc6b9_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:04:58.593981+00:00
-- url     : https://prove2.me/theorems/a910dcff-aac9-42cf-8515-b6398a77b95b
-- title:
--   Extract Euler counts from a planar augmentation
-- statement:
--   A crossing-free drawing on at least three vertices admits an augmentation on the same vertices containing every original edge, with edge and face counts satisfying connected Euler counting and the aggregate face-degree lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_counts__p2m_00de7451_7f58_447b_bbcb_462fc14bc6b9_a4 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ (K : SimpleGraph V) (e f : Nat), G.edgeSet ⊆ K.edgeSet ∧ K.edgeSet.ncard = e ∧ Fintype.card V + f = e + 2 ∧ 3 * f ≤ 2 * e := by sorry
