-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_dense
-- name    : WilliamsonShmoys.planar_completion_dense
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:33:15.989288+00:00
-- url     : https://prove2.me/theorems/3d6368d9-eaec-49d2-8b49-ded7ae1200cf
-- title:
--   Dense planar supergraph completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_dense
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
