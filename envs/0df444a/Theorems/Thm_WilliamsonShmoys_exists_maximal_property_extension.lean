-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_property_extension
-- name    : WilliamsonShmoys.exists_maximal_property_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:48:45.736029+00:00
-- url     : https://prove2.me/theorems/370dc6c2-459f-4a1c-aeb6-2e5562342463
-- title:
--   Maximal extension for a property on finite simple graphs
-- statement:
--   For any property of simple graphs on a finite vertex type, every graph satisfying the property has an extension satisfying it that is maximal among such extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_property_extension
    {V : Type} [Fintype V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hM : P M) :
    ∃ L : SimpleGraph V, M ≤ L ∧ P L ∧
      ∀ K : SimpleGraph V, L ≤ K → P K → K = L := by sorry
