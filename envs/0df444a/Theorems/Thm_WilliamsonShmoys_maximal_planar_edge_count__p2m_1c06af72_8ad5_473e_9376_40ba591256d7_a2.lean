-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:00.202818+00:00
-- url     : https://prove2.me/theorems/b8edd37c-13b1-49cd-ab2a-13ab8a4421f7
-- title:
--   A maximal planar simple graph has exactly 3n − 6 edges
-- statement:
--   An inclusion-maximal planar simple graph on at least three vertices has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj;
      H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
