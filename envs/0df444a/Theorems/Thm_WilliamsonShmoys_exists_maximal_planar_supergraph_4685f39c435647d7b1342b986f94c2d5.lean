-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_4685f39c435647d7b1342b986f94c2d5
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_4685f39c435647d7b1342b986f94c2d5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:56:20.275446+00:00
-- url     : https://prove2.me/theorems/a31ea970-ee2e-4ea6-9cea-60264341c2ed
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex type that is maximal among planar supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_4685f39c435647d7b1342b986f94c2d5
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ K' : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K' ∧
      K.edgeSet ⊆ K'.edgeSet ∧
      ∀ H : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn H →
        K'.edgeSet ⊆ H.edgeSet →
        H.edgeSet ⊆ K'.edgeSet := by sorry
