-- Prove2me | Theorems.Thm_finite_graph_property_maximal_supergraph__p2m_266b1a11_87af_4c8d_8cdc_f947960a0fd8_a1
-- name    : finite_graph_property_maximal_supergraph__p2m_266b1a11_87af_4c8d_8cdc_f947960a0fd8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:38:22.172387+00:00
-- url     : https://prove2.me/theorems/98fc4204-1185-42f8-9d24-9b96a2776006
-- title:
--   Finite-property maximal supergraph
-- statement:
--   For any property P of simple graphs on a finite linearly ordered vertex type, if K satisfies P, then K has a P-satisfying supergraph H that is maximal among P-satisfying supergraphs under edge inclusion. H contains K and therefore has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem finite_graph_property_maximal_supergraph__p2m_266b1a11_87af_4c8d_8cdc_f947960a0fd8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (P : SimpleGraph V → Prop) (hK : P K) :
    Exists fun H : SimpleGraph V => Exists fun dH : DecidableRel H.Adj =>
      P H ∧
      (forall u v, K.Adj u v → H.Adj u v) ∧
      K.edgeFinset.card ≤ (by letI : DecidableRel H.Adj := dH; exact H.edgeFinset.card) ∧
      (forall J : SimpleGraph V, P J →
        (forall u v, H.Adj u v → J.Adj u v) →
        (forall u v, J.Adj u v → H.Adj u v)) := by sorry
