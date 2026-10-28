-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_triangulation_extension_db2981d6
-- name    : WilliamsonShmoys.planarDrawingOn_triangulation_extension_db2981d6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:41:31.450372+00:00
-- url     : https://prove2.me/theorems/277de266-4239-4e53-bc35-5251bc884381
-- title:
--   Extension of a planar drawing to a triangulation
-- statement:
--   Every graph on a finite linearly ordered vertex type with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_triangulation_extension_db2981d6
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
