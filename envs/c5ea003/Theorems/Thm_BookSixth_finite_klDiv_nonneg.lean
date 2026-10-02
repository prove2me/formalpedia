-- Prove2me | Theorems.Thm_BookSixth_finite_klDiv_nonneg
-- name    : BookSixth.finite_klDiv_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T06:12:31.25425+00:00
-- url     : https://prove2.me/theorems/0d0dfd73-3e7c-4f19-a046-f8150ddffb4c
-- title:
--   Chapter 37 lemma: Gibbs inequality for finite distributions
-- statement:
--   Gibbs' inequality: the Kullback-Leibler divergence between finite probability mass functions is nonnegative when q is supported wherever p is. This is the engine of the entropy proof of the Bregman-Minc permanent bound behind the upper counting bound of Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, information-theoretic lemma for the Bregman-Minc bound, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.finite_klDiv_nonneg (α : Type*) [Fintype α] [Nonempty α] (p q : α → ℝ) (hpn : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1) (hqn : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1) (hsupp : ∀ a, p a ≠ 0 → q a ≠ 0) :
    0 ≤ ∑ a, p a * Real.log (p a / q a) := by sorry
