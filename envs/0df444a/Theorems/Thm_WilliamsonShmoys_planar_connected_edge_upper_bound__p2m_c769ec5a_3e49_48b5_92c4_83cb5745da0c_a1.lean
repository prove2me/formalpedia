-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_upper_bound__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
-- name    : WilliamsonShmoys.planar_connected_edge_upper_bound__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:18:19.968316+00:00
-- url     : https://prove2.me/theorems/b94ddc87-8e35-451a-9f65-e1e9d97b1c62
-- title:
--   Connected planar simple graph edge upper bound
-- statement:
--   A connected drawable finite simple graph with at least three vertices has at most 3|V|−6 edges. This is the connected Euler-formula step used after augmentation. A proof route is to count vertices, edges, and faces with Euler’s formula and use that each face boundary has length at least three under these hypotheses. The condition |V| ≥ 3 excludes the smaller connected cases where that face-length argument does not apply.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_upper_bound__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hConnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
