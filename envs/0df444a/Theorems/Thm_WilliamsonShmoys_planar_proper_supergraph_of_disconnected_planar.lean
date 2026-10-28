-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_proper_supergraph_of_disconnected_planar
-- name    : WilliamsonShmoys.planar_proper_supergraph_of_disconnected_planar
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:05:28.052793+00:00
-- url     : https://prove2.me/theorems/61502e58-7e3c-4bf1-bc30-f39e420a70f9
-- title:
--   Strict planar extension of a disconnected planar graph
-- statement:
--   Every disconnected planar graph on the fixed finite vertex type with at least three vertices has a strictly larger planar supergraph on that same vertex type. This isolates the geometric step from the later finite maximality argument. A proof route is to join distinct components by an arc in the complement of the existing drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_proper_supergraph_of_disconnected_planar
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hDisconnected : ¬ P.Connected) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧ P ≤ Q ∧ P ≠ Q := by
  sorry
