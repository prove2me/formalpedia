-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_81030912_3569_483c_b042_44cc0f2e2aea_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_81030912_3569_483c_b042_44cc0f2e2aea_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:30.523741+00:00
-- url     : https://prove2.me/theorems/2fffb22b-bc54-424c-9398-721fe1492b46
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Any drawable finite simple graph on at least three vertices is a subgraph of a drawable triangulation on the same vertex set, whose edge count is exactly 3|V|−6. This removes the edge-counting step from the parent; the remaining core is the geometric extension and Euler-formula argument. The hypothesis |V| ≥ 3 is essential for this exact formula (and covers the three-vertex boundary case). A proof route is to add drawable edges within faces until the embedding is maximal, establish that each face is triangular, and apply Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_81030912_3569_483c_b042_44cc0f2e2aea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel H.Adj := dH
       K.edgeFinset ⊆ H.edgeFinset) ∧
      (letI : DecidableRel H.Adj := dH
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  sorry
