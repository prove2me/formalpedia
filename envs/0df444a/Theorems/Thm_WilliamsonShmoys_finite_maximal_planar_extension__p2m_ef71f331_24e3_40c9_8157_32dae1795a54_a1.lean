-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a1
-- name    : WilliamsonShmoys.finite_maximal_planar_extension__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:56.934278+00:00
-- url     : https://prove2.me/theorems/5ee8e196-64c4-419c-bd20-94ce32b8d5fd
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_planar_extension__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧ HasPlanarDrawingOn L ∧ (∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet → HasPlanarDrawingOn M → M.edgeSet = L.edgeSet) := by sorry
