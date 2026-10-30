-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_via_maximality
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension_via_maximality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:51:13.33711+00:00
-- url     : https://prove2.me/theorems/561cc06e-e471-4e1a-a773-8d1c521595db
-- title:
--   Planar triangulation extension on the same vertex set
-- statement:
--   Every drawable finite simple graph on at least three vertices is a spanning subgraph of a drawable graph on the same vertex type with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension_via_maximality
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    Exists fun L : SimpleGraph V =>
      And (Set.Subset K.edgeSet L.edgeSet)
        (And (WilliamsonShmoys.HasPlanarDrawingOn L)
          (L.edgeSet.ncard + 6 = 3 * Fintype.card V)) := by
  sorry
