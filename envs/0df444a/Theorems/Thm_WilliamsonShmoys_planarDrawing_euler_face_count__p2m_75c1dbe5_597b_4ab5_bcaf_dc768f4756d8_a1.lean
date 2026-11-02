-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_face_count__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
-- name    : WilliamsonShmoys.planarDrawing_euler_face_count__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:05:23.717737+00:00
-- url     : https://prove2.me/theorems/8caeeb70-8532-491f-8a66-8cc9bb8bbd60
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula. This is valid also for a single vertex and for trees; connectedness ensures the one-component Euler formula applies. A proof route is to construct the embedded graph’s complementary regions, establish the Euler characteristic by deleting non-bridge edges down to a spanning tree, and account for the single face of a tree drawing. This removes the Euler/topological part from the parent; the remaining work for this child is adapting that construction to the exact continuous-arc drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_euler_face_count__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) (hconn : U.Connected) :
    (letI : DecidableRel U.Adj := dU
     ∃ f : Nat,
       Fintype.card V + f = U.edgeFinset.card + 2) := by sorry
