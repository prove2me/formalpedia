-- Prove2me | Theorems.Thm_gpy_monomialPairSum_eq_joint_sum
-- name    : gpy_monomialPairSum_eq_joint_sum
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T04:01:21.135265+00:00
-- url     : https://prove2.me/theorems/4e0faadd-3bd4-4b68-b212-fc14d3ac0a00
-- title:
--   Joint collapse of the monomial pair sum
-- statement:
--   The monomial pair sum over good pairs equals the double sum over D, E in [1, R] of mu(D) mu(E) times the monomial log-power weights times the combined local weight (the local good-count product over primes dividing lcm D E, divided by phi (lcm D E)). The modulus sum collapses because the good count vanishes unless the modulus is lcm D E. This is an unconditional algebraic regrouping; it does not evaluate the sum and does not include any twisted Mertens asymptotic.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_monomialPairSum_eq_joint_sum {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
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
          * ((∏ p ∈ (Nat.lcm D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
            / ((Nat.totient (Nat.lcm D E) : ℕ) : ℝ)) := by sorry
