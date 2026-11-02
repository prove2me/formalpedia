-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a2
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:43:36.385547+00:00
-- url     : https://prove2.me/theorems/7d68d987-db7d-4975-b61e-7d5cb057947a
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hdraw : HasPlanarDrawingOn L) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ M : SimpleGraph V,
      L.edgeFinset ⊆ M.edgeFinset ∧
      HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeFinset ⊆ N.edgeFinset →
        HasPlanarDrawingOn N →
        M.edgeFinset = N.edgeFinset := by
  sorry
