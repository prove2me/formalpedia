-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:45.699203+00:00
-- url     : https://prove2.me/theorems/f6fb613b-aa01-4441-967c-f803f1a0d2bc
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every graph with a planar drawing on a finite linearly ordered vertex type has a planar supergraph on the same vertices that is maximal among planar supergraphs under inclusion. This is true without a lower bound on the vertex count; the input graph itself is a candidate, and only finitely many simple graphs exist on the vertex type. Finite maximization of edge count gives an independent proof route.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ L ≤ M ∧
        ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M := by
  sorry
