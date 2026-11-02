-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_maximal_extension__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
-- name    : WilliamsonShmoys.planarDrawing_maximal_extension__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:00:20.810956+00:00
-- url     : https://prove2.me/theorems/266b1a11-87af-4c8d-8cdc-f947960a0fd8
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that contains all its edges and is maximal among drawable supergraphs. Its edge count is at least the original edge count. The proof route is finite maximization: there are finitely many simple graphs on V, and the candidates include K; choose a drawable candidate with maximum edge count. Any drawable supergraph of that candidate must have the same edge set. This removes the existence and inclusion work from the parent. Its boundary case is unrestricted finite V; the given drawing ensures the candidate set is nonempty. The remaining work in this child is formalizing the finite maximization and edge-set/cardinality facts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_maximal_extension__p2m_8963bb62_e14c_4266_badc_3102e502f664_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V => Exists fun dH : DecidableRel H.Adj =>
      HasPlanarDrawingOn H /\
      (forall u v, K.Adj u v -> H.Adj u v) /\
      K.edgeFinset.card <= (by letI : DecidableRel H.Adj := dH; exact H.edgeFinset.card) /\
      (forall J : SimpleGraph V, HasPlanarDrawingOn J ->
        (forall u v, H.Adj u v -> J.Adj u v) ->
        (forall u v, J.Adj u v -> H.Adj u v)) := by sorry
