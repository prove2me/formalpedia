-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_unreachable_vertices__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_unreachable_vertices__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:29:38.424903+00:00
-- url     : https://prove2.me/theorems/95b2a4a5-f4af-45e5-83a3-0810e97a8978
-- title:
--   Add an edge between components while preserving a planar drawing
-- statement:
--   Given a planar drawing and two vertices in distinct components, there is a planar supergraph on the same vertices obtained by adding exactly the edge between those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_between_unreachable_vertices__p2m_a01887ab_b605_44b6_af24_b6696d8b1f6b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (a b : V)
    (hnotReach : ¬ K.Reachable a b)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.Adj a b ∧
      ∀ u v, L.Adj u v →
        K.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by sorry
