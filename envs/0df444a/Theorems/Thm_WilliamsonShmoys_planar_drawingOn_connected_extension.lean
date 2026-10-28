-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_connected_extension
-- name    : WilliamsonShmoys.planar_drawingOn_connected_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:12:46.40799+00:00
-- url     : https://prove2.me/theorems/293fa574-3531-47b1-a6d4-29c7bc8057c8
-- title:
--   Connected planar supergraph completion
-- statement:
--   Any drawn simple graph on at least three vertices has a connected planar supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_connected_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 <= Fintype.card V) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q.Connected ∧
        P.edgeSet.ncard ≤ Q.edgeSet.ncard := by sorry
