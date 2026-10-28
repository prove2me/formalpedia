-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph_f3b6ee58
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_f3b6ee58
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:39:59.035982+00:00
-- url     : https://prove2.me/theorems/ee3e2218-30cb-4f95-94d2-18e9e955f684
-- title:
--   Every finite planar graph has a maximal planar supergraph
-- statement:
--   Every planar graph on a finite ordered vertex type is contained in a planar graph on the same vertices that has no strict planar supergraph under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_f3b6ee58
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      L.edgeSet ⊆ K.edgeSet ∧
      ∀ K' : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K' →
        K.edgeSet ⊆ K'.edgeSet →
        K'.edgeSet ⊆ K.edgeSet := by sorry
