-- Prove2me | Theorems.Thm_mme_empirical_word_probability_and_marginal
-- name    : mme_empirical_word_probability_and_marginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T03:51:31.807089+00:00
-- url     : https://prove2.me/theorems/587746bd-a732-4f02-8711-88dfc0006cbd
-- title:
--   Empirical word distributions and their coordinate marginals
-- statement:
--   For a nonempty finite word, normalized symbol-fiber counts form a probability distribution, and the pushforward along any coordinate map equals the normalized coordinate-fiber cardinality.
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2 and Section 3.10; https://arxiv.org/abs/2210.10173

import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_mme_modern_entropy_data

open scoped BigOperators

set_option autoImplicit false

theorem mme_empirical_word_probability_and_marginal
    {R I : Type*} [Fintype R] [DecidableEq R] [DecidableEq I]
    (n : ℕ) (hn : 0 < n) (f : Fin n → R) (coord : R → I) :
    let p : R → ℝ := fun r ↦
      (Fintype.card {t : Fin n // f t = r} : ℝ) / (n : ℝ)
    (∀ r, 0 ≤ p r) ∧
      (∑ r, p r = 1) ∧
      ∀ i, mme_modern_marginal coord p i =
        (Fintype.card {t : Fin n // coord (f t) = i} : ℝ) / (n : ℝ) := by
  sorry
