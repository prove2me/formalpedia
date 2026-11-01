-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_small_vertex_maximizer__p2m_707bc162_d7c2_4f63_9fb7_a67d4965e3da_a1
-- name    : WilliamsonShmoys.planar_drawing_small_vertex_maximizer__p2m_707bc162_d7c2_4f63_9fb7_a67d4965e3da_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:01.305624+00:00
-- url     : https://prove2.me/theorems/f923e6b3-807e-4a07-bcf9-ebc13c7a40e3
-- title:
--   Maximum drawable supergraph for fewer than three vertices
-- statement:
--   With fewer than three vertices, extend any drawable graph to a drawable supergraph that is maximum among all drawable graphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_small_vertex_maximizer__p2m_707bc162_d7c2_4f63_9fb7_a67d4965e3da_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (dG : DecidableRel G.Adj) (hG : HasPlanarDrawingOn G) (hsmall : Fintype.card V < 3) : ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj), HasPlanarDrawingOn Q ∧ (letI : DecidableRel G.Adj := dG; letI : DecidableRel Q.Adj := dQ; G.edgeFinset ⊆ Q.edgeFinset) ∧ (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj), HasPlanarDrawingOn K → (letI : DecidableRel Q.Adj := dQ; letI : DecidableRel K.Adj := dK; Q.edgeFinset.card ≤ K.edgeFinset.card)) := by sorry
