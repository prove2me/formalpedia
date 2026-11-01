-- Prove2me | Theorems.Thm_gpy_singSum_selberg_joint
-- name    : gpy_singSum_selberg_joint
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T04:38:35.063895+00:00
-- url     : https://prove2.me/theorems/fafe9008-cd5b-4fe7-9749-88883c196895
-- title:
--   Joint factored form of the Selberg singular sum
-- statement:
--   The Selberg singular sum (with the Selberg weight of the given degree) equals the sum over monomial indices a, b of the binomial coefficients times the monomial pair sums in their fully factored twisted-weight form. This is an unconditional algebraic regrouping of the singular sum; it does not evaluate the sum to a singular series times an integral and does not include any twisted Mertens asymptotic.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_singSum_selberg_joint {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
        (if ∏ i, d i ≤ R then
            (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
              * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
          else 0) * (if ∏ i, e i ≤ R then
            (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
              * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
          else 0)
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
            (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
              * (-(Real.log (D : ℝ) / Real.log R)) ^ a
              * (-(Real.log (E : ℝ) / Real.log R)) ^ b
              * (((∏ p ∈ (Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ True) ∧ (ab.2.isSome ↔ True) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
            / ((Nat.totient (Nat.gcd D E) : ℕ) : ℝ))
                * ((∏ p ∈ (D / Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ True) ∧ (ab.2.isSome ↔ False) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
            / ((Nat.totient (D / Nat.gcd D E) : ℕ) : ℝ))
                * ((∏ p ∈ (E / Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ False) ∧ (ab.2.isSome ↔ True) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
            / ((Nat.totient (E / Nat.gcd D E) : ℕ) : ℝ))) := by sorry
