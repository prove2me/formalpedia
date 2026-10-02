-- Prove2me | Theorems.Thm_BookSixth_latin_asymptotic_of_bounds
-- name    : BookSixth.latin_asymptotic_of_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T16:51:21.435024+00:00
-- url     : https://prove2.me/theorems/4389dcb2-96d7-4df2-bcfa-5a7313cfec98
-- title:
--   Chapter 37, Corollary lemma: Latin asymptotic from two-sided bounds
-- statement:
--   If the Latin-square count $L(n)$ satisfies the two-sided bounds of Chapter 37, Theorem 2 (below by $(n!)^{2n}/n^{n^2}$ and above by $\prod_{k=1}^n (k!)^{n/k}$ for every positive $n$), then $L(n)^{1/n^2}/n$ tends to $\exp(-2)$ as $n$ tends to infinity. This is the purely analytic passage from the counting bounds to the corollary; the counting bounds themselves are assumed as hypotheses.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Corollary: analytic passage from Theorem 2 to the Latin square asymptotic, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_asymptotic_of_bounds (hlow : ∀ n : ℕ, 0 < n → (n.factorial : ℝ) ^ (2 * n) / (n : ℝ) ^ (n * n) ≤ (latinCount n : ℝ)) (hup : ∀ n : ℕ, 0 < n → (latinCount n : ℝ) ≤ ∏ k ∈ Finset.Icc 1 n, (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ))) :
    Filter.Tendsto (fun n : ℕ => (latinCount n : ℝ) ^ (1 / (n : ℝ)^2) / (n : ℝ))
      Filter.atTop (nhds (Real.exp (-2))) := by sorry
