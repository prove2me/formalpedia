-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_supergraph
-- name    : WilliamsonShmoys.exists_planar_edge_count_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:13:35.174277+00:00
-- url     : https://prove2.me/theorems/200a044f-248b-4fd0-bcd3-c7e9d499ee78
-- title:
--   Planar graphs have a planar supergraph with the maximal edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices is a subgraph of a drawable graph on the same vertex set with exactly 3|V|−6 edges, including when the original graph is disconnected or has isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_edge_count_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
