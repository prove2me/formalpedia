-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_drawable_supergraph_max_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
-- name    : WilliamsonShmoys.finite_drawable_supergraph_max_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:00:24.017994+00:00
-- url     : https://prove2.me/theorems/fdfe37dd-8665-4b9a-b299-fea28c7c32ed
-- title:
--   A drawable supergraph maximizing finite adjacency count
-- statement:
--   Among drawable supergraphs of `G` on the same finite vertex type, there is one with maximum `Nat.card` of its ordered-adjacency subtype. The candidate set is nonempty because it contains `G`; finiteness of the type of simple graphs permits selection of a maximum. This removes the finite-selection step from the parent, which still needs the strict-inclusion cardinality result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.finite_drawable_supergraph_max_arc_count__p2m_95b85285_7ea7_4e66_8526_e78475582691_a2
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, G ≤ H → HasPlanarDrawingOn H →
        Nat.card {p : V × V // H.Adj p.1 p.2} ≤
          Nat.card {p : V × V // K.Adj p.1 p.2} := by sorry
