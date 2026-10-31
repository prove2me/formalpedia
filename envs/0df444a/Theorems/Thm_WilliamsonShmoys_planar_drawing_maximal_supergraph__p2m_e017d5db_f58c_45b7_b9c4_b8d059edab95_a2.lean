-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:48:08.200529+00:00
-- url     : https://prove2.me/theorems/707bc162-d7c2-4f63-9fb7-a67d4965e3da
-- title:
--   Maximum-edge drawable supergraph on the same vertices
-- statement:
--   For any finite drawable graph, there is a drawable supergraph on the same vertices that retains its edges and has at least as many edges as every other drawable graph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (dG : DecidableRel G.Adj) (hG : HasPlanarDrawingOn G) : ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj), HasPlanarDrawingOn Q ∧ (letI : DecidableRel G.Adj := dG; letI : DecidableRel Q.Adj := dQ; G.edgeFinset ⊆ Q.edgeFinset) ∧ (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj), HasPlanarDrawingOn K → (letI : DecidableRel Q.Adj := dQ; letI : DecidableRel K.Adj := dK; Q.edgeFinset.card ≤ K.edgeFinset.card)) := by sorry
