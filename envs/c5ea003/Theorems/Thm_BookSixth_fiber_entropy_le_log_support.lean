-- Prove2me | Theorems.Thm_BookSixth_fiber_entropy_le_log_support
-- name    : BookSixth.fiber_entropy_le_log_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T09:01:43.182744+00:00
-- url     : https://prove2.me/theorems/7b78d1ab-915d-4e09-8e9f-0b8e042eb32a
-- title:
--   Chapter 37 adapter: fiber entropy bounded by log of support size
-- statement:
--   The entropy of weights supported on S is at most the total mass times log of the support size.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, adapter lemma for the entropy proof of the Bregman-Minc bound. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.fiber_entropy_le_log_support (β : Type*) [Fintype β] [Nonempty β] (w : β → ℝ) (S : Finset β) (P : ℝ)
    (hP : 0 < P) (hnn : ∀ b, 0 ≤ w b) (hsum : ∑ b, w b = P) (hsupp : ∀ b ∉ S, w b = 0) (hne : S.Nonempty) :
    -∑ b, w b * Real.log (w b / P) ≤ P * Real.log (S.card : ℝ) := by sorry
