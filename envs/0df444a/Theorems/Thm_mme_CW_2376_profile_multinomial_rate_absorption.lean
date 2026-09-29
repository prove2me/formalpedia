-- Prove2me | Theorems.Thm_mme_CW_2376_profile_multinomial_rate_absorption
-- name    : mme_CW_2376_profile_multinomial_rate_absorption
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:25:27.549279+00:00
-- url     : https://prove2.me/theorems/6d3fafca-04af-4b9c-bf0c-e71092b197f7
-- title:
--   Absorb exact-profile multinomial and hash losses into the CW fourth-root rate
-- statement:
--   Let V be the exact multinomial number of mode words at the rational equation-(13) marginal profile. Eventually, V times the conservative finite hash loss exp(-100000 sqrt(N+1)) dominates the entropy base cw2376ProfileCountBase discounted in every coordinate by exp(-(m+1)^(-1/4)). This is a purely factorial/real-asymptotic theorem: Stirling contributes only polynomial loss, the explicit hash envelope is exp(-O(sqrt m)), while the published discount has total exponent -Theta(m^(3/4)).
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), multinomial count and normalized auxiliary expression on journal pp. 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_CW_2376_profile_induced_family
open MME Filter

theorem mme_CW_2376_profile_multinomial_rate_absorption :
    ∀ᶠ m : ℕ in atTop,
      let N := cw2376ProfileLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          (((384072 * m).factorial : ℝ) *
            ((1308290 * m).factorial : ℝ) *
            ((1231903 * m).factorial : ℝ) *
            ((75036 * m).factorial : ℝ) *
            ((699 * m).factorial : ℝ))
      (cw2376ProfileCountBase *
          Real.exp (-(cw2376ProfileRate m))) ^ N ≤
        V * Real.exp
          (-100000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  sorry
