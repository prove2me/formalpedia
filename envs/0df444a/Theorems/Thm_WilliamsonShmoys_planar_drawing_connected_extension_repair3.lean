-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_repair3
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_repair3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:02:08.439385+00:00
-- url     : https://prove2.me/theorems/4f0d9992-7573-45d4-906f-9c67b481c2dd
-- title:
--   Connect components of a planar drawing
-- statement:
--   A finite planar drawing on at least three vertices can be extended, on the same vertex set, to a connected planar supergraph with at least as many edges. The new work is the component-joining construction; prove it by joining components with arcs through the complement and use graph inclusion for edge-count monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V,
      T ≤ S ∧ HasPlanarDrawingOn S ∧ S.Connected ∧
      T.edgeSet.ncard ≤ S.edgeSet.ncard := by sorry
