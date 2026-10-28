-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_exists_maximal_supergraph
-- name    : WilliamsonShmoys.planar_completion_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:23:01.934151+00:00
-- url     : https://prove2.me/theorems/3e5a78f6-e57d-429c-b3b2-aabdf6133c06
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that has no drawable edge supergraph with a strictly larger edge set. Choose a drawable supergraph of M with maximum edge count among the finitely many simple graphs on V.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      M.edgeSet ⊆ L.edgeSet ∧
      (∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K →
        L.edgeSet ⊆ K.edgeSet → K.edgeSet = L.edgeSet) := by sorry
