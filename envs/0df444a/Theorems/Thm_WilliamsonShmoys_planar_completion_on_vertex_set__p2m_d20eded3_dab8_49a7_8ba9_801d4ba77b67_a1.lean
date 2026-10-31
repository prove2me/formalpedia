-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_on_vertex_set__p2m_d20eded3_dab8_49a7_8ba9_801d4ba77b67_a1
-- name    : WilliamsonShmoys.planar_completion_on_vertex_set__p2m_d20eded3_dab8_49a7_8ba9_801d4ba77b67_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:31:49.680657+00:00
-- url     : https://prove2.me/theorems/a5f3545b-9213-4099-bf3a-a8a2e64023e0
-- title:
--   Planar completion on a fixed vertex set
-- statement:
--   Any graph with a crossing-free drawing on a finite fixed vertex set of size at least three can be augmented, without adding vertices, to a planar graph with exactly 3|V|−6 edges. The parent applies maximality to this supergraph and transfers its edge count to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_on_vertex_set__p2m_d20eded3_dab8_49a7_8ba9_801d4ba77b67_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : LE.le 3 (Fintype.card V))
    (hT : HasPlanarDrawingOn T) :
    ∃ T' : SimpleGraph V,
      LE.le T T' ∧ HasPlanarDrawingOn T' ∧
      T'.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
