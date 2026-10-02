-- Prove2me | Theorems.Thm_BookSixth_latin_asymptotic
-- name    : BookSixth.latin_asymptotic
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-13T01:37:01.620149+00:00
-- url     : https://prove2.me/theorems/c924e4c1-5598-481f-b6f0-137b209f5a7b
-- title:
--   Chapter 37, Corollary: Latin square asymptotic
-- statement:
--   As the order n tends to infinity, L(n)^(1/n²)/n tends to exp(−2), where L(n) counts labeled Latin squares. The totalized value at n=0 has no effect on this limit.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Corollary: Latin square asymptotic, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_asymptotic  :
    Filter.Tendsto (fun n : ℕ => (latinCount n : ℝ) ^ (1 / (n : ℝ)^2) / (n : ℝ))
      Filter.atTop (nhds (Real.exp (-2))) := by sorry
