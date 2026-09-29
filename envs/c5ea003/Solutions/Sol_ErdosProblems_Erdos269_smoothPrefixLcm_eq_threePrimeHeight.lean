-- Prove2me | solution 1 for ErdosProblems.Erdos269.smoothPrefixLcm_eq_threePrimeHeight
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:28:48.998879+00:00
-- url     : https://prove2.me/submissions/6beaac28-ee8e-4160-89d4-bd6278dca58d

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Theorems.Thm_ErdosProblems_Erdos269_smooth3Val_dvd_threePrimeHeight_of_mem
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the three-prime running-LCM coordinate

This module starts the problem-owned formalization of the first unresolved
three-prime case.  It records the exact computational height used by the
running-LCM representation, its cubic majorant, the smallest non-separation
fixture for `{2,3,5}`, the variable-base tail-state update, and the uniform
quadratic bound for actual filtered smooth-number shells.

No declaration here asserts irrationality or transcendence of a three-prime
value.  The missing producer is still an infinite residue-escape or genuinely
higher-dimensional analytic theorem.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators













/-- The literal smooth-prefix LCM divides the computational height. -/
theorem smoothPrefixLcm_dvd_threePrimeHeight (p q r x : ℕ) :
    smoothPrefixLcm p q r x ∣ threePrimeHeight p q r x := by
  apply Finset.lcm_dvd
  intro e he
  exact smooth3Val_dvd_threePrimeHeight_of_mem he

/-- The pure `p` height component occurs in the actual prefix. -/
theorem pureFirst_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (Nat.log p x, 0, 0) ∈ smoothPrefixExponents p q r x := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
        Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  · simpa [smooth3Val] using Nat.pow_log_le_self p hx

/-- The pure `q` height component occurs in the actual prefix. -/
theorem pureSecond_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (0, Nat.log q x, 0) ∈ smoothPrefixExponents p q r x := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_self _),
        Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  · simpa [smooth3Val] using Nat.pow_log_le_self q hx

/-- The pure `r` height component occurs in the actual prefix. -/
theorem pureThird_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (0, 0, Nat.log r x) ∈ smoothPrefixExponents p q r x := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
        Finset.mem_range.mpr (Nat.lt_succ_self _)⟩
  · simpa [smooth3Val] using Nat.pow_log_le_self r hx
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x := by
  apply Nat.dvd_antisymm (smoothPrefixLcm_dvd_threePrimeHeight p q r x)
  have hpDvd : p ^ Nat.log p x ∣ smoothPrefixLcm p q r x := by
    simpa [smoothPrefixLcm, smooth3Val] using
      (Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureFirst_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx))
  have hqDvd : q ^ Nat.log q x ∣ smoothPrefixLcm p q r x := by
    simpa [smoothPrefixLcm, smooth3Val] using
      (Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureSecond_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx))
  have hrDvd : r ^ Nat.log r x ∣ smoothPrefixLcm p q r x := by
    simpa [smoothPrefixLcm, smooth3Val] using
      (Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureThird_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx))
  have hpqCoprime :
      (p ^ Nat.log p x).Coprime (q ^ Nat.log q x) :=
    Nat.coprime_pow_primes _ _ hp hq hpq
  have hprCoprime :
      (p ^ Nat.log p x).Coprime (r ^ Nat.log r x) :=
    Nat.coprime_pow_primes _ _ hp hr hpr
  have hqrCoprime :
      (q ^ Nat.log q x).Coprime (r ^ Nat.log r x) :=
    Nat.coprime_pow_primes _ _ hq hr hqr
  have hpqDvd :
      p ^ Nat.log p x * q ^ Nat.log q x ∣ smoothPrefixLcm p q r x :=
    hpqCoprime.mul_dvd_of_dvd_of_dvd hpDvd hqDvd
  have hpqrCoprime :
      (p ^ Nat.log p x * q ^ Nat.log q x).Coprime
        (r ^ Nat.log r x) :=
    Nat.coprime_mul_iff_left.mpr ⟨hprCoprime, hqrCoprime⟩
  exact hpqrCoprime.mul_dvd_of_dvd_of_dvd hpqDvd hrDvd
