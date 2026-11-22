-- Prove2me | solution 1 for Erdos390.prime_power_column_valuation_error_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-16T14:02:15.808765+00:00
-- url     : https://prove2.me/submissions/8d5ebafc-9c81-42e4-8a34-2416a67d0690

import Definitions.Def_erdos390_prime_power_rounding
open scoped BigOperators
open Erdos390.WholePaper

/- Adapted from the pinned source cited in the explanation. -/
namespace Erdos390.WholePaper
noncomputable section

def primeExponentRange (p M : ℕ) : Finset ℕ :=
  Finset.Icc 1 (Nat.log p M)

private theorem factorization_le_log_of_le
    {a M p : ℕ} (ha : 0 < a) (haM : a ≤ M) (hp : p.Prime) :
    a.factorization p ≤ Nat.log p M := by
  have hpowDvd : p ^ (a.factorization p) ∣ a :=
    (hp.pow_dvd_iff_le_factorization ha.ne').mpr le_rfl
  have hpowLe : p ^ (a.factorization p) ≤ a :=
    Nat.le_of_dvd ha hpowDvd
  exact (Nat.le_log_of_pow_le hp.one_lt hpowLe).trans
    (Nat.log_mono_right haM)

/-- The admissible global column attached to an exponent in
`primeExponentRange p M`. -/
def primePowerColumnOf {p M : ℕ} (hp : p.Prime) (hM : 0 < M)
    (j : ↥(primeExponentRange p M)) : ↥(primePowerColumns M) := by
  have hj : 1 ≤ j.1 := (Finset.mem_Icc.mp j.2).1
  have hjlog : j.1 ≤ Nat.log p M := (Finset.mem_Icc.mp j.2).2
  have hpow : p ^ j.1 ≤ M := Nat.pow_le_of_le_log hM.ne' hjlog
  have hp_le_pow : p ≤ p ^ j.1 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right hp.pos hj
  exact ⟨(p, j.1), mem_primePowerColumns.mpr
    ⟨hp.two_le, hp_le_pow.trans hpow, hj,
      hjlog.trans (Nat.log_le_self p M), hp, hpow⟩⟩

private theorem factorization_cast_eq_sum_indicators
    {a M p : ℕ} (ha : 0 < a) (haM : a ≤ M) (hp : p.Prime) :
    (a.factorization p : ℝ) =
      ∑ j ∈ primeExponentRange p M,
        if p ^ j ∣ a then (1 : ℝ) else 0 := by
  classical
  have hfac : a.factorization p ≤ Nat.log p M :=
    factorization_le_log_of_le ha haM hp
  have hfilter :
      (primeExponentRange p M).filter (fun j ↦ p ^ j ∣ a) =
        Finset.Icc 1 (a.factorization p) := by
    ext j
    simp only [primeExponentRange, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj, _⟩, hdvd⟩
      exact ⟨hj, (hp.pow_dvd_iff_le_factorization ha.ne').mp hdvd⟩
    · rintro ⟨hj, hjfac⟩
      exact ⟨⟨hj, hjfac.trans hfac⟩,
        (hp.pow_dvd_iff_le_factorization ha.ne').mpr hjfac⟩
  calc
    (a.factorization p : ℝ) =
        ((Finset.Icc 1 (a.factorization p)).card : ℝ) := by simp
    _ = (((primeExponentRange p M).filter
        (fun j ↦ p ^ j ∣ a)).card : ℝ) := by rw [hfilter]
    _ = ∑ j ∈ primeExponentRange p M,
        if p ^ j ∣ a then (1 : ℝ) else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- The exact valuation-error box obtained by summing the individual
prime-power column discrepancies. -/
theorem roundingValuationError_le
    {A : Type*} [Fintype A]
    (value : A → ℕ) (M d : ℕ) (X x : A → ℝ)
    (hM : 0 < M)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hcolumn : ∀ q : ↥(primePowerColumns M),
      |∑ a, (X a - x a) *
        zeroOneColumn
          (fun q' a' ↦ primePowerInc M q' (value a')) q a| ≤
        (4 * d : ℝ))
    {p : ℕ} (hp : p.Prime) :
    |roundingValuationError value X x p| ≤
      (4 * d * Nat.log p M : ℝ) := by
  classical
  have herror : roundingValuationError value X x p =
      ∑ j ∈ (primeExponentRange p M).attach,
        ∑ a, (X a - x a) *
          zeroOneColumn
            (fun q' a' ↦ primePowerInc M q' (value a'))
            (primePowerColumnOf hp hM j) a := by
    simp only [roundingValuationError]
    calc
      (∑ a, (X a - x a) * (value a).factorization p) =
          ∑ a, (X a - x a) *
            (∑ j ∈ primeExponentRange p M,
              if p ^ j ∣ value a then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← factorization_cast_eq_sum_indicators
          (hvaluePos a) (hvalueLe a) hp]
      _ = ∑ a, ∑ j ∈ primeExponentRange p M,
            (X a - x a) *
              (if p ^ j ∣ value a then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      _ = ∑ j ∈ primeExponentRange p M, ∑ a,
            (X a - x a) *
              (if p ^ j ∣ value a then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ j ∈ (primeExponentRange p M).attach, ∑ a,
            (X a - x a) *
              (if p ^ j.1 ∣ value a then (1 : ℝ) else 0) := by
        exact (Finset.sum_attach (primeExponentRange p M)
          (fun j ↦ ∑ a, (X a - x a) *
            (if p ^ j ∣ value a then (1 : ℝ) else 0))).symm
      _ = ∑ j ∈ (primeExponentRange p M).attach,
          ∑ a, (X a - x a) *
            zeroOneColumn
              (fun q' a' ↦ primePowerInc M q' (value a'))
              (primePowerColumnOf hp hM j) a := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro a _
        change
          (X a - x a) * (if p ^ j.1 ∣ value a then (1 : ℝ) else 0) =
            (X a - x a) * zeroOneColumn
              (fun q' a' ↦ primePowerInc M q' (value a'))
              (primePowerColumnOf hp hM j) a
        simp [zeroOneColumn, primePowerInc, primePowerColumnOf]
  rw [herror]
  calc
    |∑ j ∈ (primeExponentRange p M).attach,
        ∑ a, (X a - x a) *
          zeroOneColumn
            (fun q' a' ↦ primePowerInc M q' (value a'))
            (primePowerColumnOf hp hM j) a| ≤
        ∑ j ∈ (primeExponentRange p M).attach,
          |∑ a, (X a - x a) *
            zeroOneColumn
              (fun q' a' ↦ primePowerInc M q' (value a'))
              (primePowerColumnOf hp hM j) a| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ (primeExponentRange p M).attach, (4 * d : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact hcolumn (primePowerColumnOf hp hM j)
    _ = (4 * d * Nat.log p M : ℝ) := by
      simp [primeExponentRange]
      ring


end
end Erdos390.WholePaper

theorem solution
    {A : Type*} [Fintype A]
    (value : A → ℕ) (M d : ℕ) (X x : A → ℝ)
    (hM : 0 < M)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hcolumn : ∀ q : ↥(primePowerColumns M),
      |∑ a, (X a - x a) *
        zeroOneColumn
          (fun q' a' ↦ primePowerInc M q' (value a')) q a| ≤
        (4 * d : ℝ))
    {p : ℕ} (hp : p.Prime) :
    |roundingValuationError value X x p| ≤
      (4 * d * Nat.log p M : ℝ) := by
  exact roundingValuationError_le value M d X x hM hvaluePos hvalueLe hcolumn hp
