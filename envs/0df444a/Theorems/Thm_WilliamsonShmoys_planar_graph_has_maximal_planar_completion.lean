-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_completion
-- name    : WilliamsonShmoys.planar_graph_has_maximal_planar_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:17:19.376608+00:00
-- url     : https://prove2.me/theorems/1d810103-6bdc-40b5-924c-e9e8f0fd8321
-- title:
--   Edge-maximal planar completion on the same vertices
-- statement:
--   Every connected planar graph on at least three vertices is contained in a planar graph on the same vertices to which no further edge can be added while preserving planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_maximal_planar_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists H' : SimpleGraph V,
      H <= H' ∧
      WilliamsonShmoys.HasPlanarDrawingOn H' ∧
      (∀ K : SimpleGraph V, H' <= K → K ≠ H' →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn K) := by sorry
