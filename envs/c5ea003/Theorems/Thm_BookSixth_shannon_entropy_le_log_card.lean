-- Prove2me | Theorems.Thm_BookSixth_shannon_entropy_le_log_card
-- name    : BookSixth.shannon_entropy_le_log_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T05:57:23.957357+00:00
-- url     : https://prove2.me/theorems/faff6100-072b-45b6-9a20-37cbf255c419
-- title:
--   Chapter 37 lemma: finite Shannon entropy is maximized by the uniform distribution
-- statement:
--   Gibbs' inequality for finite distributions: the Shannon entropy of a probability mass function on a nonempty finite type is at most the log of the cardinality, with equality for the uniform distribution. This is the information-theoretic input to the entropy proof of the Bregman-Minc permanent bound behind the upper counting bound of Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, information-theoretic lemma for the Bregman-Minc bound, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.shannon_entropy_le_log_card (α : Type*) [Fintype α] [Nonempty α] (p : α → ℝ) (hnn : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    -∑ a, p a * Real.log (p a) ≤ Real.log (Fintype.card α) := by sorry
