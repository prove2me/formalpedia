-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
-- name    : WilliamsonShmoys.planar_drawable_maximal_extension__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:26.33752+00:00
-- url     : https://prove2.me/theorems/28aa14c5-09a5-4ce3-a139-0c8dcdfcfd9a
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs. The finite set of possible edge sets gives a proof route by maximizing edge count among drawable extensions of W. This removes the finite extension choice from the parent; the maximality quantifies over all drawable supergraphs on the fixed vertex type. The remaining core obligation is the edge-count theorem for maximal drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_maximal_extension__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
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
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         T.edgeFinset ⊆ U.edgeFinset) →
        (letI : DecidableRel T.Adj := dT
         letI : DecidableRel U.Adj := dU
         U.edgeFinset ⊆ T.edgeFinset)) := by sorry
