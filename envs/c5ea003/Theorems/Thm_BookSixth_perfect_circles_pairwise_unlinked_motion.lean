-- Prove2me | Theorems.Thm_BookSixth_perfect_circles_pairwise_unlinked_motion
-- name    : BookSixth.perfect_circles_pairwise_unlinked_motion
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T11:51:19.590986+00:00
-- url     : https://prove2.me/theorems/f6a7245e-187d-4a69-8b49-100cf7e4a1cc
-- title:
--   Chapter 15, Theorem 1: pairwise-unlinked perfect circles have a separating perfect-circle motion
-- statement:
--   This is the geometric motion form of Chapter 15, Theorem 1. If finitely many disjoint perfect circles in $\mathbb{R}^3$ are pairwise unlinked, there is one ambient isotopy which starts at the identity, sends the components to the separated standard circles, and keeps every image a perfect circle throughout the motion. The source proof uses spherical domes above the disks bounded by the circles: pairwise-unlinked circles have disjoint domes, and slicing the four-dimensional dome construction by time gives the required motion.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, pp. 99-103, the spherical-dome proof of the perfect-circle motion theorem. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.perfect_circles_pairwise_unlinked_motion 
    {m : ℕ} (C : Fin m → Set Space3)
    (hround : ∀ i, RoundCircle (C i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hpairs : ∀ i j, i ≠ j → IsUnlink (![C i, C j] : Fin 2 → Set Space3)) :
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (∀ i, (K 1) '' C i = standardCircle i.val) ∧
      (∀ t i, RoundCircle ((K t) '' C i)) := by sorry
