-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_of_disconnected_of_card_ge_three
-- name    : WilliamsonShmoys.planar_extension_of_disconnected_of_card_ge_three
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:41:42.421069+00:00
-- url     : https://prove2.me/theorems/43e8bba7-fd16-4b65-bf1b-9671e26ddb54
-- title:
--   A disconnected planar graph on at least three vertices has a planar proper edge extension
-- statement:
--   A disconnected graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn can be extended by at least one edge while retaining such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_of_disconnected_of_card_ge_three
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet ≠ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  sorry
