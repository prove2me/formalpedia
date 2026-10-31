-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_completion__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
-- name    : WilliamsonShmoys.planar_drawing_has_edge_maximal_completion__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:52.893639+00:00
-- url     : https://prove2.me/theorems/0cefbc89-9ee6-49b2-9b84-ef741e6aba70
-- title:
--   Finite edge-maximal drawable completion
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that has no proper drawable simple supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_edge_maximal_completion__p2m_7cf6806e_5be6_4790_8cad_719b856f9dab_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ (∀ L : SimpleGraph V, (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by sorry
