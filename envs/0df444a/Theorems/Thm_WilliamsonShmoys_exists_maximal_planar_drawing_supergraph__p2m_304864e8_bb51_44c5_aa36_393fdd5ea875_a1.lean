-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:49:26.245991+00:00
-- url     : https://prove2.me/theorems/62b43b1c-617a-4c66-9ae5-73016cbc3161
-- title:
--   Existence of a maximal planar drawing supergraph
-- statement:
--   Every finite planar drawing has a planar supergraph on the same vertices that is maximal under strict edge-set inclusion. Finiteness permits choosing a planar supergraph with a maximal number of edges; this removes the finite maximization step from the parent and can be proved by maximizing edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) : ∃ Y : SimpleGraph V, X.edgeSet ⊆ Y.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧ ∀ Z : SimpleGraph V, Y.edgeSet ⊂ Z.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn Z := by sorry
