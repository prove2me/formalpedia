-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count__p2m_3b189e66_afee_4feb_9bd4_e20d54522d03_a3
-- name    : WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_3b189e66_afee_4feb_9bd4_e20d54522d03_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:37.312795+00:00
-- url     : https://prove2.me/theorems/af412bdb-08d3-443e-9526-1f4e854292c2
-- title:
--   Same-vertex planar completion with exact edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices with exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_3b189e66_afee_4feb_9bd4_e20d54522d03_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
