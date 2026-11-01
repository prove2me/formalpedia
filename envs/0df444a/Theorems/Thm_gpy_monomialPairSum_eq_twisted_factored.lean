-- Prove2me | Theorems.Thm_gpy_monomialPairSum_eq_twisted_factored
-- name    : gpy_monomialPairSum_eq_twisted_factored
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T04:23:00.599831+00:00
-- url     : https://prove2.me/theorems/61758c16-2f78-42e6-b48a-b3b1a53f29e6
-- title:
--   Fully factored twisted-weight form of the monomial pair sum
-- statement:
--   The monomial pair sum equals the double sum over D, E in [1, R] of mu(D) mu(E) times the monomial log-power weights times a product of three twisted one-variable weights: the both-sided weight at gcd D E, the D-only weight at D / gcd D E, and the E-only weight at E / gcd D E. The mu factors kill the non-squarefree pairs, so the squarefree factorization applies to every surviving term. This is an unconditional algebraic factorization; it does not evaluate the sum and does not include any twisted Mertens asymptotic.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_monomialPairSum_eq_twisted_factored {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
        (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
          * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
          * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
          * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
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
