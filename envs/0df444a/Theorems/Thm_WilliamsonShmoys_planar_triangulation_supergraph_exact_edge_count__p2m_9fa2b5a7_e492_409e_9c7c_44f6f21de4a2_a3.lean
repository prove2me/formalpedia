-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a3
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:08:12.993216+00:00
-- url     : https://prove2.me/theorems/bba3ebb6-f48a-40f6-8fc3-19f0d2d80e0e
-- title:
--   Exact edge-count drawable completion
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained, on that same vertex type, in a drawable graph with exactly 3n − 6 edges. The condition n ≥ 3 covers the triangle boundary case and is needed for the stated exact count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V,
      G.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
