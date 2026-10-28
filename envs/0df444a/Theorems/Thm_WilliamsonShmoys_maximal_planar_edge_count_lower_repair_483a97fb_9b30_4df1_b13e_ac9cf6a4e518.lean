-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:49:11.837426+00:00
-- url     : https://prove2.me/theorems/a3780995-02f0-4c2f-a98c-6e5f167c3de5
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex type and with at least three vertices has at least 3|V| − 6 edges. Triangulating nontriangular faces by adding drawable diagonals contradicts maximality unless the graph is already triangulated; the three-vertex case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hNmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
