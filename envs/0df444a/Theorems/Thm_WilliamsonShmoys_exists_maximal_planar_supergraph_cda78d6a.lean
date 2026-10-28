-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_cda78d6a
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_cda78d6a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:32:15.15518+00:00
-- url     : https://prove2.me/theorems/e684855b-b79f-4fc0-b3d3-049426e89191
-- title:
--   A finite planar graph has a maximal planar supergraph on the same vertices
-- statement:
--   Every finite graph with a planar drawing has an inclusion-maximal drawable supergraph on the same vertex type. No lower bound on the vertex count is needed for this finite maximality step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_cda78d6a
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDrawing : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by
  sorry
