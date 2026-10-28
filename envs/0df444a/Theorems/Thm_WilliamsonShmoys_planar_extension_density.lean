-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_density
-- name    : WilliamsonShmoys.planar_extension_density
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:23:31.882859+00:00
-- url     : https://prove2.me/theorems/8b6262cf-afb8-48cb-948e-a428a96643e9
-- title:
--   Drawable graphs admit a dense drawable extension
-- statement:
--   Every crossing-free drawing of a finite simple graph on at least three vertices can be extended, without changing its vertex set, to a crossing-free drawable supergraph with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_extension_density
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
