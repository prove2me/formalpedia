-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_sparse_extension_maximal_drawable_supergraph__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1
-- name    : WilliamsonShmoys.planar_sparse_extension_maximal_drawable_supergraph__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:05:31.29319+00:00
-- url     : https://prove2.me/theorems/8f1c26ef-2f0a-4462-8f1e-8e571e7f9b9e
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type is contained in a drawable supergraph that has no strict drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_sparse_extension_maximal_drawable_supergraph__p2m_8878012f_4621_4e20_8c97_e8aa106c5519_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (K : SimpleGraph U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph U,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph U, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
