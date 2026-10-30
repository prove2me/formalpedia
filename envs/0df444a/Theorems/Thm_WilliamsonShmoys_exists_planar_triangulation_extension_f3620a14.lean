-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_f3620a14
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension_f3620a14
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:59:16.254827+00:00
-- url     : https://prove2.me/theorems/e1760f10-7304-4cb1-aaa2-27dc7f18fe2d
-- title:
--   Planar triangulation extension on the same vertex type
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertex type having exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_triangulation_extension_f3620a14
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      T ≤ S ∧
      S.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
