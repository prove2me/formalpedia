-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:31:17.159179+00:00
-- url     : https://prove2.me/theorems/31724b24-6486-4b90-a7f9-e54f1195bcbf
-- title:
--   A maximal planar simple graph has exactly 3n − 6 edges
-- statement:
--   A simple graph on at least three vertices that is maximal among planar supergraphs on the same vertex type has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
