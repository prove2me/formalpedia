-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_supergraph__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
-- name    : WilliamsonShmoys.edge_maximal_planar_supergraph__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:11:49.31477+00:00
-- url     : https://prove2.me/theorems/2c13f176-83f3-43cd-bbd0-841f438f66be
-- title:
--   Existence of an edge maximal drawable supergraph
-- statement:
--   Every drawable graph on the given finite vertex type is contained in a drawable supergraph with no proper drawable supergraph on those vertices. Prove this by maximizing the edge count over the finite collection of drawable supergraphs containing G.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_supergraph__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
