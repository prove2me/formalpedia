-- Prove2me | Theorems.Thm_mme_stothers_remaining_four_optimizer_certificates
-- name    : mme_stothers_remaining_four_optimizer_certificates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:57:20.059304+00:00
-- url     : https://prove2.me/theorems/ccf8eb66-c382-47dd-a2c6-31fa6ba1de7f
-- title:
--   Davie--Stothers optimizer certificates for phi_125, phi_134, phi_224, and phi_233
-- statement:
--   Assume positive real parameters satisfy the Davie--Stothers order regime 16 ≤ E < H < L < 4H, together with the two exact cross-multiplied inequalities needed in the phi_224 case. Then the explicit normalized profiles chosen in Lemma 5.1(ii)--(v) are feasible and their binary or ternary entropy products simplify exactly to the four displayed endpoints for phi_125, phi_134, phi_224, and phi_233. This isolates the complete optimizer-substitution layer from the finite hashing and tensor-extraction arguments.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(ii)--(v), pp. 364--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Real

set_option autoImplicit false

theorem mme_stothers_remaining_four_optimizer_certificates
    (E H L : ℝ) (h16E : 16 ≤ E) (hEH : E < H)
    (hHL : H < L) (hL4H : L < 4 * H)
    (h224left : (2 + E) * L ≤ 2 * H * (E + H))
    (h224right : 2 * E * H ≤ L * (2 + E + H)) :
    (let a := L / (L + E * H)
     let b := L / (L + 2 * H)
     0 < a ∧ 0 < b ∧ a + b ≤ 1 ∧
       4 / H *
          ((L / a) ^ a * ((E * H) / (1 - a)) ^ (1 - a)) *
          ((L / b) ^ b * ((2 * H) / (1 - b)) ^ (1 - b)) =
        4 * (L + E * H) * (2 * H + L) / H) ∧
    (let sigma := L / (E + L)
     let a := 2 / (2 + 2 * E + H)
     let c := H / (2 + 2 * E + H)
     0 < a ∧ 0 < c ∧ c ≤ sigma ∧ sigma + a ≤ 1 ∧
       8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c)) =
        4 * (E + L) * (2 + 2 * E + H)) ∧
    (let sigma := 2 * H / (2 * H + L)
     let a := 2 / (2 + 2 * E + H)
     let b := 2 * E / (2 + 2 * E + H)
     0 < a ∧ 0 < b ∧
       a + b / 2 ≤ sigma ∧ sigma ≤ 1 - b / 2 ∧
       (((2 * H) / sigma) ^ sigma *
          (L / (1 - sigma)) ^ (1 - sigma)) ^ (2 : ℕ) *
        (((2 / H) / a) ^ a *
          ((2 * E / H) / b) ^ b *
          (1 / (1 - a - b)) ^ (1 - a - b)) =
        (2 * H + L) ^ (2 : ℕ) * (2 + 2 * E + H) / H) ∧
    (let sigma := (2 * H / L) / (2 * H / L + 1)
     let mu := (E / L) / (E / L + 1)
     0 < sigma ∧ 0 < mu ∧ sigma + 2 * mu ≤ 2 ∧
       4 * L ^ (2 : ℕ) *
          (((2 * H / L) / sigma) ^ sigma *
            (1 / (1 - sigma)) ^ (1 - sigma)) *
          (((E / L) / mu) ^ mu *
            (1 / (1 - mu)) ^ (1 - mu)) ^ (2 : ℕ) =
        4 * (E + L) ^ (2 : ℕ) * (2 * H + L) / L) := by
  sorry
