-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_extension__p2m_4f14f4e8_9a22_49bc_9255_581b0400575d_a1
-- name    : WilliamsonShmoys.planar_drawable_supergraph_extension__p2m_4f14f4e8_9a22_49bc_9255_581b0400575d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:18:25.267703+00:00
-- url     : https://prove2.me/theorems/a34c08da-0825-4948-8969-f4152e2e6bf4
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type that is maximal under edge inclusion. This isolates the fixed-vertex topological completion and finite maximality argument from the edge count. A proof route is to maximize the edge set among drawable supergraphs on the fixed vertex set, after proving that the allowed drawing representation is preserved under the necessary planar edge additions. Check component and face-boundary cases in that drawing-extension argument; merely asserting that disconnected components can always be joined does not supply it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_supergraph_extension__p2m_4f14f4e8_9a22_49bc_9255_581b0400575d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, HasPlanarDrawingOn N ∧ M ≤ N ∧
      ∀ K : SimpleGraph V, HasPlanarDrawingOn K → N ≤ K → K ≤ N → N = K := by sorry
