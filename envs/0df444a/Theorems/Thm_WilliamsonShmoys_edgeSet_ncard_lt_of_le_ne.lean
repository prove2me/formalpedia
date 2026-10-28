-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_le_ne
-- name    : WilliamsonShmoys.edgeSet_ncard_lt_of_le_ne
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:24:47.622043+00:00
-- url     : https://prove2.me/theorems/5d99bc95-b525-489a-8fe6-5ed1fd8adcf9
-- title:
--   Strict graph extension increases finite edge count
-- statement:
--   For graphs on a finite vertex type, proper inclusion of graphs strictly increases the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_lt_of_le_ne
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H) (hne : G ≠ H) :
    G.edgeSet.ncard < H.edgeSet.ncard := by sorry
