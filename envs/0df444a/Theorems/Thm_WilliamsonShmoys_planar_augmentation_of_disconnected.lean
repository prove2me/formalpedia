-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_of_disconnected
-- name    : WilliamsonShmoys.planar_augmentation_of_disconnected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:56:07.511037+00:00
-- url     : https://prove2.me/theorems/f8f2afbc-d892-4037-a052-a76e61426eb3
-- title:
--   A disconnected planar drawing admits a strict drawable augmentation
-- statement:
--   This new lemma performs the geometric step needed by the parent: a finite drawable graph on at least three vertices that is disconnected has a strict drawable supergraph on the same vertex set. Starting from the given drawing, choose two distinct components incident to a common face and draw a connecting arc in that face, with interior disjoint from the existing drawing. This removes the need for the parent to reason about drawing arcs; the remaining obligation is the face-incidence and arc-construction argument for the supplied arbitrary-arc definition. The cardinality hypothesis is retained from the parent and rules out degenerate empty vertex cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_augmentation_of_disconnected {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) (hDisconnected : ¬ L.Connected) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ L ≠ M := by sorry
