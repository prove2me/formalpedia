-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count__p2m_b8edd37c_13b1_49cd_ab2a_13ab8a4421f7_a1
-- name    : WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_b8edd37c_13b1_49cd_ab2a_13ab8a4421f7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:32:49.317348+00:00
-- url     : https://prove2.me/theorems/a4284538-7636-40d4-87e5-69297326a38c
-- title:
--   Planar completion to a triangulation on the same vertex set
-- statement:
--   Every finite simple graph with at least three vertices and a drawing of the specified kind has a supergraph on the same vertex set that also has such a drawing and has exactly 3n - 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_b8edd37c_13b1_49cd_ab2a_13ab8a4421f7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : ∀ L : SimpleGraph V, DecidableRel L.Adj := fun L => Classical.decRel L.Adj;
        K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
