-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_of_hereditary__p2m_cf95c127_ee46_41b0_beca_773ede50ca42_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph_of_hereditary__p2m_cf95c127_ee46_41b0_beca_773ede50ca42_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:24:23.84662+00:00
-- url     : https://prove2.me/theorems/615834e8-7beb-4bca-b090-73db6237ddd9
-- title:
--   Finite maximal supergraph for a hereditary graph property
-- statement:
--   On a finite ordered vertex type, every graph satisfying a hereditary property has a supergraph satisfying that property which is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph_of_hereditary__p2m_cf95c127_ee46_41b0_beca_773ede50ca42_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (hHer : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) (X : SimpleGraph V) (hX : P X) : ∃ Y : SimpleGraph V, X ≤ Y ∧ P Y ∧ ∀ Z : SimpleGraph V, Y ≤ Z → P Z → Z = Y := by sorry
