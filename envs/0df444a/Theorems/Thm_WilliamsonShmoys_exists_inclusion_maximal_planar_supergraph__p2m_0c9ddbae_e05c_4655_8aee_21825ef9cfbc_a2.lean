-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:39:25.713481+00:00
-- url     : https://prove2.me/theorems/057e14c2-934b-4aed-8cca-6104aec3bbaf
-- title:
--   Existence of an inclusion maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices with no drawable strict supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ¬ ∃ N : SimpleGraph V, M.edgeSet ⊂ N.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
