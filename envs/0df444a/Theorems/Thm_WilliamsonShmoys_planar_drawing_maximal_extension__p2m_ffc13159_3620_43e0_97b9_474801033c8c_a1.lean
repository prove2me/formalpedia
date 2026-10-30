-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:19.049906+00:00
-- url     : https://prove2.me/theorems/bb57e846-d9a4-493d-944c-0498086a1fa4
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under graph inclusion. The finite collection of simple graphs supplies a maximal candidate, and the original graph ensures the collection is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by sorry
