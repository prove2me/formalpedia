-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_for_certificate_38ffb807
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_for_certificate_38ffb807
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:55:07.268469+00:00
-- url     : https://prove2.me/theorems/e23f071b-28cb-4595-a1ae-f688eec15cd4
-- title:
--   Connected extension of a drawn planar graph on at least three vertices
-- statement:
--   For a finite ordered vertex type with at least three vertices, every graph with a crossing-free drawing has a connected crossing-free supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_for_certificate_38ffb807
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
