-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_supergraph__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1
-- name    : WilliamsonShmoys.planar_graph_has_maximal_supergraph__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:40:37.858986+00:00
-- url     : https://prove2.me/theorems/9a3db19b-bf7e-423a-a744-a0ca4f49e085
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under inclusion. Finiteness of the possible simple graphs permits choosing an extension with the largest edge set; any strict drawable extension would contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_maximal_supergraph__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
