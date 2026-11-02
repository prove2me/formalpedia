-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a2
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:09.195254+00:00
-- url     : https://prove2.me/theorems/9798e73d-8bce-431e-b549-81f1b82e41b6
-- title:
--   Exact edge-count drawable completion
-- statement:
--   Every graph with a drawing under `HasPlanarDrawingOn` and at least three vertices is contained, on the same vertex type, in a drawable graph with exactly 3n−6 edges. The bound n ≥ 3 is essential to this exact count; the n = 3 case permits K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a2
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
