-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:55.422029+00:00
-- url     : https://prove2.me/theorems/0006c745-fe2e-4a7f-b8e7-0e6ae6383a33
-- title:
--   Existence of an inclusion-maximal drawn supergraph
-- statement:
--   Any finite drawn simple graph has an inclusion-maximal supergraph on the same vertex type that still admits a drawing. The explicit edge-set inclusion is included for the parent’s cardinality comparison.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_826e5589_6c55_45ce_83c1_aa1fee8116e2_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet ⊆ H.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
