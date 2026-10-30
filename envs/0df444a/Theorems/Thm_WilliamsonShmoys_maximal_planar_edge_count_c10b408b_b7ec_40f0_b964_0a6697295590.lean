-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_c10b408b_b7ec_40f0_b964_0a6697295590
-- name    : WilliamsonShmoys.maximal_planar_edge_count_c10b408b_b7ec_40f0_b964_0a6697295590
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:17:55.671522+00:00
-- url     : https://prove2.me/theorems/23341804-e9bd-4849-9be7-9e709bd142a9
-- title:
--   A maximal drawable graph has the exact planar edge count
-- statement:
--   If a drawable simple graph on at least three vertices has no strictly larger drawable supergraph on the same vertices, it has exactly 3|V|−6 edges. The lower bound is necessary for this claim; maximal drawable graphs on fewer vertices need not have that count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_c10b408b_b7ec_40f0_b964_0a6697295590
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
