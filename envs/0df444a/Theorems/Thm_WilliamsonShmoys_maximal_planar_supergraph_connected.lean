-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected
-- name    : WilliamsonShmoys.maximal_planar_supergraph_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:02:36.561305+00:00
-- url     : https://prove2.me/theorems/85d53c0c-737c-477f-b1f6-79b2d9e304de
-- title:
--   A maximal drawable supergraph is connected
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on those vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ M : SimpleGraph V,
      K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.Connected := by sorry
