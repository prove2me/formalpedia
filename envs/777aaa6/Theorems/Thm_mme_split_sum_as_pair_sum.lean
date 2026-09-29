-- Prove2me | Theorems.Thm_mme_split_sum_as_pair_sum
-- name    : mme_split_sum_as_pair_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T18:52:13.726113+00:00
-- url     : https://prove2.me/theorems/53813301-9844-428c-9a45-816d68c050aa
-- title:
--   Sums over admissible splits as double sums over two grades
-- statement:
--   A sum over the admissible splits of a parent grade triple is a double sum over the first two grades.
--
--   An admissible split of `half` inside a parent triple is a triple of grades summing to `half`, each at most the parent's. Such a triple is determined by its first two entries, so summing a function of the three grades over all admissible splits is the same as summing over all pairs of values below `half`, with the third grade taken to be the remainder. The only hypothesis is that the summand vanishes on triples that are not admissible, which makes the inadmissible pairs contribute nothing.
-- source:
--   General finite-sum identity used for the recursive regional data of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349). No exponent claim.

import Mathlib
import Definitions.Def_mme_recursive_thin_split_data
open BigOperators MME
open scoped Classical
set_option autoImplicit false

theorem mme_split_sum_as_pair_sum {half : ℕ} {par : Fin 3 → ℕ} {M : Type*} [AddCommMonoid M]
    (g : ℕ → ℕ → ℕ → M)
    (hg : ∀ a b c : ℕ, ¬ (a + b + c = half ∧ a ≤ par 0 ∧ b ≤ par 1 ∧ c ≤ par 2) → g a b c = 0) :
    ∑ x : RecursiveThinSplit.Split half par, g (x.val 0).val (x.val 1).val (x.val 2).val =
      ∑ a : Fin (half + 1), ∑ b : Fin (half + 1), g a.val b.val (half - a.val - b.val) := by sorry
