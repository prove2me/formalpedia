-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_bridge__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
-- name    : WilliamsonShmoys.planar_drawing_component_bridge__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:18.619405+00:00
-- url     : https://prove2.me/theorems/b2249a9b-0ed4-4e0a-b974-67058e424e5f
-- title:
--   Planar drawing admits a bridge between components
-- statement:
--   If a finite graph with at least three vertices has a planar drawing and is disconnected, it has a planar supergraph containing an edge between vertices that were in different connected components. The independent geometric route is to use the finite embedded drawing to find a connecting arc in the complement, while preserving the existing vertex and edge drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_component_bridge__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by sorry
