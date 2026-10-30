-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:20.043982+00:00
-- url     : https://prove2.me/theorems/1ac371b8-74a6-4c5b-8210-feb02fc1166e
-- title:
--   Every drawable finite graph has a maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph is contained, on the same vertices, in a drawable graph with no strictly larger drawable simple supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_fda861fd_855b_4561_971f_8551142822a0_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P) : ∃ Q : SimpleGraph V, P.edgeSet ⊆ Q.edgeSet ∧ HasPlanarDrawingOn Q ∧ (∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → HasPlanarDrawingOn R → R = Q) := by sorry
