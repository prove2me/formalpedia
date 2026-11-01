-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:28:07.5582+00:00
-- url     : https://prove2.me/theorems/74778092-2591-4f0d-adff-b80207b549ce
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Any drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under adjacency inclusion. The finite collection of simple graphs on the vertex type permits a maximality argument; this child does not require a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ u v, L.Adj u v → M.Adj u v) ∧
      ∀ N : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn N →
        (∀ u v, M.Adj u v → N.Adj u v) → N = M := by sorry
