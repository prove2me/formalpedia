-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:19:47.48106+00:00
-- url     : https://prove2.me/theorems/c7b07ed7-db7c-450f-a64f-c5e3047d491b
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that is maximal under edge inclusion among drawable supergraphs. The original graph makes the finite candidate collection nonempty; maximizing edge count gives maximality. This handles disconnected starting graphs as well. Its hypotheses preserve the exact drawing and finite ordered vertex setting of the parent. The remaining work is to formalize the finite choice and edge-set comparison.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun (L : SimpleGraph V) => Exists fun (dL : DecidableRel L.Adj) =>
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      K.edgeFinset ⊆ L.edgeFinset /\
      (∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn M →
        L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset = L.edgeFinset) := by
  sorry
