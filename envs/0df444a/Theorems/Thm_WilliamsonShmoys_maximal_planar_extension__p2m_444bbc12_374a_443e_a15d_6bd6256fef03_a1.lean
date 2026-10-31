-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:10:29.321587+00:00
-- url     : https://prove2.me/theorems/cf95c127-ee46-41b0-beca-773ede50ca42
-- title:
--   Maximal drawable supergraph on the fixed vertex set
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) : ∃ Y : SimpleGraph V, X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧ ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y := by sorry
