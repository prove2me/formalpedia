-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension_7607aed3
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension_7607aed3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:00:40.997195+00:00
-- url     : https://prove2.me/theorems/78e0c5c1-a649-4b43-abc1-9cf86e20510e
-- title:
--   Maximal drawable supergraph extension for triangulation
-- statement:
--   Every connected finite graph with a planar drawing has an inclusion-maximal drawable supergraph on the same vertex set, and that supergraph remains connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal_extension_7607aed3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧ K.Connected ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) := by sorry
