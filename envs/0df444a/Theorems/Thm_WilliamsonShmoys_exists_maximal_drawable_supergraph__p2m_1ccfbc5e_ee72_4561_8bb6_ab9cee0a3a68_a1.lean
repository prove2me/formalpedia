-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:52:58.687208+00:00
-- url     : https://prove2.me/theorems/1113193c-c471-4877-96ad-488654c7dac4
-- title:
--   Every drawable finite graph has a maximal drawable supergraph on the same vertices
-- statement:
--   Any drawable simple graph on a finite ordered vertex type is contained in a drawable supergraph on the same vertices that has no strict drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_1ccfbc5e_ee72_4561_8bb6_ab9cee0a3a68_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdrawing : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
