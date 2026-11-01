-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_extension_max_edge_cardinality__p2m_28aa14c5_09a5_4ce3_a139_0c8dcdfcfd9a_a2
-- name    : WilliamsonShmoys.planar_drawable_extension_max_edge_cardinality__p2m_28aa14c5_09a5_4ce3_a139_0c8dcdfcfd9a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:34:39.835192+00:00
-- url     : https://prove2.me/theorems/b4aaeeba-e5a6-45aa-97e8-7edbd004c7d2
-- title:
--   Maximum edge count among drawable extensions
-- statement:
--   There is a drawable supergraph T of W whose edge count is at least that of every drawable supergraph of W. The proof route is to maximize edgeFinset.card over the finite, nonempty collection of drawable extensions; W itself witnesses nonemptiness. This removes the finite maximal-choice argument from the parent. The remaining core obligation is to formalize that finite maximization for SimpleGraph V and its edgeFinset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_extension_max_edge_cardinality__p2m_28aa14c5_09a5_4ce3_a139_0c8dcdfcfd9a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (dW : DecidableRel W.Adj)
    (hW : HasPlanarDrawingOn W) :
    ∃ (T : SimpleGraph V) (dT : DecidableRel T.Adj),
      HasPlanarDrawingOn T ∧
      (letI : DecidableRel W.Adj := dW
       letI : DecidableRel T.Adj := dT
       W.edgeFinset ⊆ T.edgeFinset) ∧
      (∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
        HasPlanarDrawingOn U →
        (letI : DecidableRel W.Adj := dW
         letI : DecidableRel U.Adj := dU
         W.edgeFinset ⊆ U.edgeFinset) →
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         U.edgeFinset.card ≤ T.edgeFinset.card)) := by sorry
