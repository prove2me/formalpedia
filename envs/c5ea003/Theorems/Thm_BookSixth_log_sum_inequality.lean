-- Prove2me | Theorems.Thm_BookSixth_log_sum_inequality
-- name    : BookSixth.log_sum_inequality
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T06:48:48.515529+00:00
-- url     : https://prove2.me/theorems/5a76dfd4-a858-4dbe-90a2-e678401a040a
-- title:
--   Chapter 37 adapter: log-sum inequality for entropy assembly
-- statement:
--   Log-sum inequality: for positive weights a, b, A*log(A/B) <= sum a_i log(a_i/b_i). Gibbs corollary driving the per-row entropy bounds in the Bregman-Minc route.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Gibbs/log-sum engine for the entropy route to Bregman-Minc, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.log_sum_inequality (ι : Type*) [Fintype ι] [Nonempty ι] (a b : ι → ℝ)
    (hapos : ∀ i, 0 < a i) (hbpos : ∀ i, 0 < b i) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i))
      ≤ ∑ i, a i * Real.log (a i / b i) := by sorry
