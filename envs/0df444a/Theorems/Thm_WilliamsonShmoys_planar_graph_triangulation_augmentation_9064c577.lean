-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_augmentation_9064c577
-- name    : WilliamsonShmoys.planar_graph_triangulation_augmentation_9064c577
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:58:23.603334+00:00
-- url     : https://prove2.me/theorems/916edde4-5d52-427d-a09f-c7184a62a0db
-- title:
--   A connected planar graph admits a triangulating augmentation
-- statement:
--   Every connected drawable simple graph on at least three vertices can be augmented, without adding vertices, to a drawable triangulation with exactly 3n−6 edges. Prove this by finite face-by-face augmentation to a maximal planar embedding and Euler's formula. The boundary n=3 is included; connectedness and the cardinality hypothesis are retained.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_triangulation_augmentation_9064c577
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
