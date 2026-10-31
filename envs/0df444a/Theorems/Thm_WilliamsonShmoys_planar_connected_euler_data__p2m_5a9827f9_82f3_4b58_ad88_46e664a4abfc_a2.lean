-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_euler_data__p2m_5a9827f9_82f3_4b58_ad88_46e664a4abfc_a2
-- name    : WilliamsonShmoys.planar_connected_euler_data__p2m_5a9827f9_82f3_4b58_ad88_46e664a4abfc_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:41:53.797112+00:00
-- url     : https://prove2.me/theorems/de18ee44-a6cd-4180-b2a3-27479832bde2
-- title:
--   Euler and face-length data for a connected planar graph
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there is a natural face count satisfying Euler’s formula and the inequality that three times the face count is at most twice the edge count. The order and size hypotheses exclude the connected one-edge graph, whose sole face boundary would have length two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_euler_data__p2m_5a9827f9_82f3_4b58_ad88_46e664a4abfc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hConnected : M.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
        3 * f ≤ 2 * M.edgeSet.ncard := by sorry
