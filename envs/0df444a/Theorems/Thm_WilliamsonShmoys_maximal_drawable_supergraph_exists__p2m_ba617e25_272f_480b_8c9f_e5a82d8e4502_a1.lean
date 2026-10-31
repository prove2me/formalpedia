-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:33:33.136069+00:00
-- url     : https://prove2.me/theorems/9d4b50c3-15e8-4543-a111-5c4919504785
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Among drawable simple supergraphs of M on the same finite vertex type, there is one that has no proper drawable supergraph on that vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_ba617e25_272f_480b_8c9f_e5a82d8e4502_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hCard : 3 ≤ Fintype.card V) : ∃ S : SimpleGraph V, M ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧ ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by sorry
