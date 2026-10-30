-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_20261026
-- name    : WilliamsonShmoys.maximal_planar_edge_count_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:44:34.970919+00:00
-- url     : https://prove2.me/theorems/890b5f05-c27e-4ec4-a294-5ad57945cee7
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal planar graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, J ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
