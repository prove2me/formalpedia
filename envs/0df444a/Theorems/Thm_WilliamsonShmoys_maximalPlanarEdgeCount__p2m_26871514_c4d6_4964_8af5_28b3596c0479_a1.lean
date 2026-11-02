-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarEdgeCount__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
-- name    : WilliamsonShmoys.maximalPlanarEdgeCount__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:23:13.960196+00:00
-- url     : https://prove2.me/theorems/22365758-ec9b-4f13-a59a-216cdd6c8044
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   A planar simple graph on at least three vertices that has no proper planar supergraph on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarEdgeCount__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K →
      (letI : DecidableRel N.Adj := dN
       letI : DecidableRel K.Adj := dK
       N.edgeFinset ⊆ K.edgeFinset) →
      N = K) :
    letI : DecidableRel N.Adj := dN
    N.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
