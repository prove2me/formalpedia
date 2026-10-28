-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_euler
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count_euler
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:26:24.89379+00:00
-- url     : https://prove2.me/theorems/99b4482c-9ffd-493a-8117-2e2d6e5dc751
-- title:
--   Edge count of a maximal planar supergraph by Euler’s formula
-- statement:
--   An inclusion-maximal planar graph on a finite ordered vertex type with at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (U X : SimpleGraph V)
    (hmax : WilliamsonShmoys.IsPlanarMaximalSupergraphForEdgeCountCompletion U X)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by sorry
