-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:26.962862+00:00
-- url     : https://prove2.me/theorems/f100cac1-01af-43d8-b482-631795dea89f
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite graph has an inclusion-maximal drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) : ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧ (∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R) := by sorry
