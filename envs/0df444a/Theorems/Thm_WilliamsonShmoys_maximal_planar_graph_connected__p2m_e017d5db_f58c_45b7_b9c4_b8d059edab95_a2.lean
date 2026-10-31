-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_connected__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:48:09.830901+00:00
-- url     : https://prove2.me/theorems/34185d2c-6d62-41c0-8a17-2791b9e1cd5d
-- title:
--   A maximum-edge drawable graph is connected
-- statement:
--   A drawable graph on at least two vertices that maximizes the number of edges among drawable graphs on those vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_connected__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj) (hcard : 2 ≤ Fintype.card V) (hQ : HasPlanarDrawingOn Q) (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj), HasPlanarDrawingOn K → (letI : DecidableRel Q.Adj := dQ; letI : DecidableRel K.Adj := dK; Q.edgeFinset.card ≤ K.edgeFinset.card)) : Q.Connected := by sorry
