-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augment_below_triangulation_bound_36583a35
-- name    : WilliamsonShmoys.planar_augment_below_triangulation_bound_36583a35
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:48:50.714639+00:00
-- url     : https://prove2.me/theorems/f80e2fd1-f4fd-41b5-b8a2-80f8fe680055
-- title:
--   Augmentation below the planar triangulation bound for this completion theorem
-- statement:
--   A drawable finite simple graph on at least three vertices with fewer than 3|V|−6 edges has a drawable strict supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_augment_below_triangulation_bound_36583a35
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hBelow : (K.edgeSet.ncard : Int) <
      3 * (Fintype.card V : Int) - 6) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ ¬ L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
