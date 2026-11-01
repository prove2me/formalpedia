-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion__p2m_03d1095c_703e_4187_9b91_3791c513ec62_a2
-- name    : WilliamsonShmoys.maximal_planar_completion__p2m_03d1095c_703e_4187_9b91_3791c513ec62_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:12:50.62193+00:00
-- url     : https://prove2.me/theorems/bb1eb53b-a90c-47ce-9dd0-93bdb2c805fc
-- title:
--   Completion of a finite drawable graph to a triangulation
-- statement:
--   Every drawable simple graph on a finite vertex type of size at least three is a subgraph of a drawable graph on the same vertex type with exactly `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_completion__p2m_03d1095c_703e_4187_9b91_3791c513ec62_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧ HasPlanarDrawingOn Y ∧
      (letI : DecidableRel Y.Adj := Classical.decRel Y.Adj
       3 * Fintype.card V - 6 = Y.edgeFinset.card) := by sorry
