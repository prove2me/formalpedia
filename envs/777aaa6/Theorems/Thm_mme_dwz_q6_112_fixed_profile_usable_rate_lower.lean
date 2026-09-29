-- Prove2me | Theorems.Thm_mme_dwz_q6_112_fixed_profile_usable_rate_lower
-- name    : mme_dwz_q6_112_fixed_profile_usable_rate_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T13:56:05.175691+00:00
-- url     : https://prove2.me/theorems/3bbfead0-be5c-4744-9af9-bd368cf69fca
-- title:
--   Exact q=6 Table-2 112 profile capacity with square-root loss
-- statement:
--   At the exact q=6 Table-2 112 profile N=50,000,000t, L=21,015t, and G=49,978,985t, the finite multinomial capacity times the component volume dominates the printed 112 component base raised to the full source power, up to an explicit square-root-exponential loss.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3, Table 2, and Appendix A (Lemma 4.6(d)).

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data

open MME MME.DWZSquare

set_option autoImplicit false

theorem mme_dwz_q6_112_fixed_profile_usable_rate_lower
    (tau C : ℝ) (t : ℕ) (ht : 0 < t) :
    let N : ℕ := 50000000 * t
    let L : ℕ := 21015 * t
    let G : ℕ := 49978985 * t
    let Z : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
    let X : ℕ := Nat.choose N G
    let B : ℕ := Nat.choose (2 * G) G
    let capacity : ℝ :=
      ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
    let loss : ℝ :=
      Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ)))
    let volume : ℝ :=
      ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau)
    (componentBase tau (12 : Fin 15) ^ 3) ^ (2 * N) *
        Real.exp (-((32 * (6 : ℝ) ^ 7 *
            ((14 : ℕ).factorial : ℝ)) + 5 * C) *
          Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
      capacity * loss ^ 5 * volume := by
  sorry
