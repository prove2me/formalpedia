-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_density_8b6262cf
-- name    : WilliamsonShmoys.maximal_planar_extension_density_8b6262cf
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:33:28.027+00:00
-- url     : https://prove2.me/theorems/ff7c9ff8-0a1c-4df0-abf1-b97d1d2ffeec
-- title:
--   A maximal drawable graph has the planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension_density_8b6262cf
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      L.edgeSet = H.edgeSet) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
