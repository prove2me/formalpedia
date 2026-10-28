-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_core
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_core
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:18:42.177186+00:00
-- url     : https://prove2.me/theorems/b837152a-765e-4e30-8f05-4765469f71be
-- title:
--   Connected planar extension of a finite drawing
-- statement:
--   Any finite graph with the given planar drawing and at least three vertices has a connected planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_core
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V,
      T ≤ S ∧ HasPlanarDrawingOn S ∧ S.Connected := by sorry
