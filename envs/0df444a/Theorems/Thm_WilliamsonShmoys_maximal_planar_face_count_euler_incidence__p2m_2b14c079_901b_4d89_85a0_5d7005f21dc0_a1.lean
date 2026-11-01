-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_euler_incidence__p2m_2b14c079_901b_4d89_85a0_5d7005f21dc0_a1
-- name    : WilliamsonShmoys.maximal_planar_face_count_euler_incidence__p2m_2b14c079_901b_4d89_85a0_5d7005f21dc0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:58:21.716194+00:00
-- url     : https://prove2.me/theorems/877a68bf-2408-4570-9e48-0da03981c44d
-- title:
--   Face count equations for an edge-maximal planar graph
-- statement:
--   For a finite edge-maximal graph with the supplied crossing-free drawing and at least three vertices, there is a natural number of faces satisfying Euler’s equation and the triangular face-edge incidence equation. The first equation is |V| + f = |E| + 2; the second is 2|E| = 3f.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_count_euler_incidence__p2m_2b14c079_901b_4d89_85a0_5d7005f21dc0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hmax : ∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      HasPlanarDrawingOn W →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset ⊆ W.edgeFinset) →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       W.edgeFinset ⊆ U.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     ∃ f : Nat, Fintype.card V + f = U.edgeFinset.card + 2 ∧
       2 * U.edgeFinset.card = 3 * f) := by sorry
