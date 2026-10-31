-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_isMaximalPlanarSupergraph__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
-- name    : WilliamsonShmoys.exists_isMaximalPlanarSupergraph__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:54:16.102748+00:00
-- url     : https://prove2.me/theorems/af13f63f-cd05-40af-9e3b-bd5fcae2a11f
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every graph with a drawing as defined in the target is contained in an inclusion-maximal graph with such a drawing on the same finite vertex type. The finite collection of simple graphs on V makes an inclusion-maximal planar supergraph exist; this does not require the vertex-count lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_isMaximalPlanarSupergraph__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
