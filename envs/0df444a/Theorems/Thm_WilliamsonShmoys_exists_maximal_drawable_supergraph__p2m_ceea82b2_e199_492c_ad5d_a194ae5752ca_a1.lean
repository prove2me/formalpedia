-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:23.769983+00:00
-- url     : https://prove2.me/theorems/dde6c772-1281-4d21-9b54-46ae763d0262
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that has no strictly larger drawable supergraph on that type. This removes the finite selection step from the parent; choose among the finitely many simple graphs by edge count, with G as a candidate. There is no vertex-count boundary condition because this selection step is valid for every finite vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ W : SimpleGraph V, G ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧ ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = W := by sorry
