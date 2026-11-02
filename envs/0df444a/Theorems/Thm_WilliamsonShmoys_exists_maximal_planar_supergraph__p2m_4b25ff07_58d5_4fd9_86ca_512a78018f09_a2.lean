-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:00:27.489756+00:00
-- url     : https://prove2.me/theorems/53969dc0-2cdb-48b1-a3db-2780f07eafb0
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex set that is maximal under edge inclusion among drawable supergraphs. Prove this by maximizing edge count among the finite family of such graphs; if a drawable supergraph strictly contained more edges, it would contradict maximality of the count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    ∃ L : SimpleGraph V,
      K.edgeFinset ⊆ L.edgeFinset ∧
      HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeFinset ⊆ M.edgeFinset →
        HasPlanarDrawingOn M →
        M.edgeFinset = L.edgeFinset := by
  sorry
