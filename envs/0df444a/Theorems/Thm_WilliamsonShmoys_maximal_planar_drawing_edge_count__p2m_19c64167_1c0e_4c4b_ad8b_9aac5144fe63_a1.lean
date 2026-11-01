-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:20:26.181684+00:00
-- url     : https://prove2.me/theorems/59af2a64-91cf-46d1-b8e7-3ca96fc0b24b
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite ordered vertices has exactly 3|V|−6 edges. The proof reduces maximality to triangular faces and applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_19c64167_1c0e_4c4b_ad8b_9aac5144fe63_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U →
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) →
      T = U)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel T.Adj := dT
    T.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
