-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_136dc8a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_136dc8a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:46:38.347034+00:00
-- url     : https://prove2.me/theorems/0b53e067-2921-4c52-bfe1-58ac0c49a4a4
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A graph on at least three finite ordered vertices that admits the stated drawing and has no proper planar supergraph on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_136dc8a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
