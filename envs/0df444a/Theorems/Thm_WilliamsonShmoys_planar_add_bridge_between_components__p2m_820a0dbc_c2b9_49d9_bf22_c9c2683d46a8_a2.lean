-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_bridge_between_components__p2m_820a0dbc_c2b9_49d9_bf22_c9c2683d46a8_a2
-- name    : WilliamsonShmoys.planar_add_bridge_between_components__p2m_820a0dbc_c2b9_49d9_bf22_c9c2683d46a8_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:08:02.339118+00:00
-- url     : https://prove2.me/theorems/a01887ab-b605-44b6-af24-b6696d8b1f6b
-- title:
--   Add a single bridge between components of a drawable graph
-- statement:
--   A finite disconnected graph with a planar drawing has a planar supergraph on the same vertices formed by adding exactly one edge between two distinct previously nonadjacent vertices. Choose endpoints incident to the unbounded faces of their components and route the new edge through the unbounded face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_bridge_between_components__p2m_820a0dbc_c2b9_49d9_bf22_c9c2683d46a8_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) (hdis : ¬ K.Connected) :
    ∃ a b : V, a ≠ b ∧ ¬ K.Adj a b ∧
      ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.Adj a b ∧
        ∀ u v, L.Adj u v →
          K.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by sorry
