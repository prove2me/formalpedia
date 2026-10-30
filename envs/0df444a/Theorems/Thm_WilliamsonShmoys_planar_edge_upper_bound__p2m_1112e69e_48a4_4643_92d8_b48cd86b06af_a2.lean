-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:04:38.408772+00:00
-- url     : https://prove2.me/theorems/9011127c-6876-47eb-ac9e-306fd8c6abcc
-- title:
--   Euler upper bound for a drawable simple graph
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3V−6 edges. This child supplies the Euler upper bound used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (M : SimpleGraph C.supp)
    [Fintype C.supp]
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ C.supp.ncard) :
    M.edgeSet.ncard + 6 ≤ 3 * C.supp.ncard := by sorry
