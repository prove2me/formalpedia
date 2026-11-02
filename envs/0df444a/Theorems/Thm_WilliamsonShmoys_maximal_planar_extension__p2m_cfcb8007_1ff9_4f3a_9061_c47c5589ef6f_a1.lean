-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_cfcb8007_1ff9_4f3a_9061_c47c5589ef6f_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_cfcb8007_1ff9_4f3a_9061_c47c5589ef6f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:05:34.285555+00:00
-- url     : https://prove2.me/theorems/15a542b2-5d3b-464a-bec6-5f7385b1f62b
-- title:
--   Existence of a maximal planar extension on the same vertices
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs, in the sense that any drawable graph containing it has no additional edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension__p2m_cfcb8007_1ff9_4f3a_9061_c47c5589ef6f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      HasPlanarDrawingOn M ∧
      (∀ u v, L.Adj u v → M.Adj u v) ∧
      (∀ N : SimpleGraph V, HasPlanarDrawingOn N →
        (∀ u v, M.Adj u v → N.Adj u v) →
        ∀ u v, N.Adj u v → M.Adj u v) := by sorry
