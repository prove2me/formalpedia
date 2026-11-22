-- Prove2me | solution 1 for Erdos390.WholePaper.exists_eventually_bankOrdinarySmoothBulkDonors_lower
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:07:25.987883+00:00
-- url     : https://prove2.me/submissions/c245ce10-7552-41fc-97be-be2aab4eb54f

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

/- Source module: Erdos390.WholePaper.BankOrdinaryDonorSupply -/
section


/-!
# Analytic supply for the ordinary bank

This file supplies the analytic half of the ordinary marker--donor argument.
The only prime-number input is the already audited cumulative estimate
`FriableAsymptotic.exists_primeLogSumUpTo_error_bound 3`.  We first turn its
two endpoint errors into a lower bound for an actual finite prime interval.
We then count the literal smooth donor window, sum the resulting occurrences,
and pass the exact marker-fiber bound through
`bankOccurrenceCeilDiv_le_markerCount`.

No asymptotic assertion is stored in a structure or accepted as a field.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.FriableAsymptotic

noncomputable section

/-! ## A cumulative-theta short-interval lemma -/











/-! ## The literal smooth donor window -/









private theorem bankOrdinaryBulkDonorIntegers_nonempty
    {Q : ℚ} (hQ : 20 < Q) :
    (bankOrdinaryBulkDonorIntegers Q).Nonempty := by
  have hQ0 : 0 ≤ Q := le_of_lt (by linarith : 0 < Q)
  have hgap : 7 * Q / 5 < 29 * Q / 20 - 1 := by linarith
  have hfloor : 29 * Q / 20 - 1 < (⌊29 * Q / 20⌋₊ : ℚ) :=
    Nat.sub_one_lt_floor _
  have hceil : ⌈7 * Q / 5⌉₊ ≤ ⌊29 * Q / 20⌋₊ := by
    apply Nat.ceil_le.mpr
    exact (hgap.trans hfloor).le
  exact ⟨⌈7 * Q / 5⌉₊, by
    simp [bankOrdinaryBulkDonorIntegers, hceil]⟩

private theorem bankOrdinaryBulkDonorIntegers_card_lower
    {Q : ℚ} (hQ : 100 ≤ Q) :
    (Q : ℝ) / 25 ≤ (bankOrdinaryBulkDonorIntegers Q).card := by
  have hQ20 : 20 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hQ0 : 0 ≤ Q := by linarith
  have hfloor :
      (29 * Q / 20 : ℚ) - 1 < (⌊29 * Q / 20⌋₊ : ℚ) :=
    Nat.sub_one_lt_floor _
  have hceil :
      (⌈7 * Q / 5⌉₊ : ℚ) < 7 * Q / 5 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  rw [bankOrdinaryBulkDonorIntegers, Nat.card_Icc]
  have hle : ⌈7 * Q / 5⌉₊ ≤ ⌊29 * Q / 20⌋₊ + 1 := by
    have hbase : ⌈7 * Q / 5⌉₊ ≤ ⌊29 * Q / 20⌋₊ := by
      apply Nat.ceil_le.mpr
      exact (by linarith : 7 * Q / 5 ≤ (⌊29 * Q / 20⌋₊ : ℚ))
    omega
  rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
  have hcast :
      ((Q : ℝ) / 25) ≤
        ((⌊29 * Q / 20⌋₊ : ℕ) : ℝ) + 1 -
          ((⌈7 * Q / 5⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast (show
      (Q / 25 : ℚ) ≤
        (⌊29 * Q / 20⌋₊ : ℚ) + 1 -
          (⌈7 * Q / 5⌉₊ : ℚ) by
      linarith)
  simpa only [Nat.cast_ofNat] using hcast

/-- Below twice the smoothness cutoff, failure of smoothness forces the
integer itself to be a prime above the cutoff. -/
private theorem prime_of_bulkDonor_not_smooth
    {n u : ℕ} {Q : ℚ} (hQ : 20 < Q)
    (hQY : Q ≤ (yNat n : ℚ))
    (hu : u ∈ bankOrdinaryBulkDonorIntegers Q)
    (hnot : u ∉ Nat.smoothNumbers (yNat n + 1)) :
    u.Prime := by
  have hQ0 : 0 ≤ Q := by linarith
  have huWindow := (mem_bankOrdinaryBulkDonorIntegers hQ0).mp hu
  have hYpos : 0 < yNat n := by
    have : (20 : ℚ) < yNat n := hQ.trans_le hQY
    exact_mod_cast (show (0 : ℚ) < yNat n by linarith)
  have huPos : 0 < u := by
    have hposQ : (0 : ℚ) < 7 * Q := by positivity
    have huQ : (0 : ℚ) < u := by linarith [huWindow.1]
    exact_mod_cast huQ
  have huTwoY : u < 2 * yNat n := by
    have huQ : (u : ℚ) ≤ 29 * Q / 20 := by linarith [huWindow.2]
    have : (u : ℚ) < 2 * (yNat n : ℚ) := by
      have hYQ : (Q : ℚ) ≤ yNat n := hQY
      nlinarith
    exact_mod_cast this
  rw [Nat.mem_smoothNumbers'] at hnot
  push_neg at hnot
  obtain ⟨p, hp, hpdiv, hpLarge⟩ := hnot
  have hYp : yNat n < p := by omega
  have hpTwo : u < 2 * p := huTwoY.trans_le (Nat.mul_le_mul_left 2 hYp.le)
  rcases hpdiv with ⟨k, rfl⟩
  have hkPos : 0 < k := by
    by_contra hk
    simp only [Nat.not_lt, Nat.le_zero] at hk
    subst k
    simp at huPos
  have hkTwo : k < 2 := by
    apply (Nat.mul_lt_mul_left hp.pos).mp
    simpa only [Nat.mul_comm] using hpTwo
  have hk : k = 1 := by omega
  simpa only [hk, Nat.mul_one] using hp

/-- Exact loss estimate for smooth donors: every excluded donor injects into
the primes up to the upper endpoint of the donor window. -/
theorem bankOrdinaryBulkDonor_card_le_smooth_add_primeCounting
    {n : ℕ} {Q : ℚ} (hQ : 20 < Q)
    (hQY : Q ≤ (yNat n : ℚ)) :
    (bankOrdinaryBulkDonorIntegers Q).card ≤
      (bankOrdinarySmoothBulkDonors n Q).card +
        Nat.primeCounting ⌊29 * Q / 20⌋₊ := by
  let rough := (bankOrdinaryBulkDonorIntegers Q).filter
    fun u ↦ u ∉ Nat.smoothNumbers (yNat n + 1)
  have hrough : rough.card ≤ Nat.primeCounting ⌊29 * Q / 20⌋₊ := by
    have hmap : Set.MapsTo id (↑rough : Set ℕ)
        (↑((⌊29 * Q / 20⌋₊ + 1).primesBelow) : Set ℕ) := by
      intro u hu
      change u ∈ rough at hu
      have huData := Finset.mem_filter.mp hu
      have huPrime := prime_of_bulkDonor_not_smooth hQ hQY
        huData.1 huData.2
      have huUpper := (Finset.mem_Icc.mp huData.1).2
      change u ∈ (⌊29 * Q / 20⌋₊ + 1).primesBelow
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, huPrime⟩
    have hinj : Set.InjOn id (↑rough : Set ℕ) :=
      Set.injOn_id (↑rough : Set ℕ)
    have hcard := Finset.card_le_card_of_injOn id hmap hinj
    simpa only [Nat.primeCounting, Nat.primeCounting',
      Nat.count_eq_card_filter_range, Nat.primesBelow] using hcard
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := bankOrdinaryBulkDonorIntegers Q)
    (fun u ↦ u ∈ Nat.smoothNumbers (yNat n + 1))
  change
    (bankOrdinarySmoothBulkDonors n Q).card + rough.card =
      (bankOrdinaryBulkDonorIntegers Q).card at hpartition
  omega

private theorem yNat_tendsto_atTop :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
      tendsto_natCast_atTop_atTop
  exact tendsto_nat_floor_atTop.comp hy

/-- Uniform positive density of smooth donor cofactors throughout the moving
range `20 < Q ≤ floor(n^(2/9))`.  The proof is literal: for large `Q` it
subtracts the Chebyshev upper bound for the nonsmooth primes, and for the
bounded remaining range eventual smoothness is exact. -/
theorem exists_eventually_bankOrdinarySmoothBulkDonors_lower :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (yNat n : ℚ) →
          delta * (Q : ℝ) ≤
            (bankOrdinarySmoothBulkDonors n Q).card := by
  let A : ℝ := Real.log 4 + 1
  have hA : 0 < A := by
    dsimp only [A]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hprimeReal := Chebyshev.eventually_primeCounting_le
    (by norm_num : (0 : ℝ) < 1)
  have hlogReal : ∀ᶠ x : ℝ in atTop, 145 * A ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (145 * A))
  have hprimeNat : ∀ᶠ m : ℕ in atTop,
      (Nat.primeCounting m : ℝ) ≤
        A * (m : ℝ) / Real.log (m : ℝ) := by
    have h := tendsto_natCast_atTop_atTop.eventually hprimeReal
    filter_upwards [h] with m hm
    simpa only [Nat.floor_natCast, A] using hm
  have hlogNat : ∀ᶠ m : ℕ in atTop,
      145 * A ≤ Real.log (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  rw [eventually_atTop] at hprimeNat hlogNat
  obtain ⟨R₁, hR₁⟩ := hprimeNat
  obtain ⟨R₂, hR₂⟩ := hlogNat
  let R : ℕ := max 100 (max R₁ R₂)
  have hR100 : 100 ≤ R := le_max_left _ _
  have hRpos : 0 < R := by omega
  let delta : ℝ := 1 / (100 * (R : ℝ))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  refine ⟨delta, hdelta, ?_⟩
  have hYevent :
      ∀ᶠ n : ℕ in atTop, ⌈29 * (R : ℚ) / 20⌉₊ ≤ yNat n :=
    yNat_tendsto_atTop.eventually
      (eventually_ge_atTop ⌈29 * (R : ℚ) / 20⌉₊)
  filter_upwards [hYevent] with n hYn
  intro Q hQ hQY
  have hQ0 : 0 ≤ Q := by linarith
  by_cases hlarge : (R : ℚ) ≤ Q
  · have hQ100 : (100 : ℚ) ≤ Q := by
      have h100R : (100 : ℚ) ≤ (R : ℚ) := by exact_mod_cast hR100
      exact h100R.trans hlarge
    have hraw := bankOrdinaryBulkDonorIntegers_card_lower hQ100
    let B : ℕ := ⌊29 * Q / 20⌋₊
    have hRB : R ≤ B := by
      apply Nat.le_floor
      have : (R : ℚ) ≤ 29 * Q / 20 := by nlinarith
      exact this
    have hR₁B : R₁ ≤ B :=
      (le_max_left R₁ R₂).trans
        ((le_max_right 100 (max R₁ R₂)).trans hRB)
    have hR₂B : R₂ ≤ B :=
      (le_max_right R₁ R₂).trans
        ((le_max_right 100 (max R₁ R₂)).trans hRB)
    have hpi := hR₁ B hR₁B
    have hlog := hR₂ B hR₂B
    have hBupperQ : (B : ℚ) ≤ 29 * Q / 20 := by
      exact Nat.floor_le (by positivity : 0 ≤ 29 * Q / 20)
    have hBupper : (B : ℝ) ≤ 29 * (Q : ℝ) / 20 := by
      exact_mod_cast hBupperQ
    have hlogPos : 0 < Real.log (B : ℝ) := lt_of_lt_of_le
      (mul_pos (by norm_num) hA) hlog
    have hpiSmall : (Nat.primeCounting B : ℝ) ≤ (Q : ℝ) / 100 := by
      calc
        (Nat.primeCounting B : ℝ) ≤
            A * (B : ℝ) / Real.log (B : ℝ) := hpi
        _ ≤ A * (29 * (Q : ℝ) / 20) / (145 * A) := by
          gcongr
        _ = (Q : ℝ) / 100 := by field_simp [hA.ne']; ring
    have hloss := bankOrdinaryBulkDonor_card_le_smooth_add_primeCounting
      hQ hQY
    have hsmooth :
        3 * (Q : ℝ) / 100 ≤
          (bankOrdinarySmoothBulkDonors n Q).card := by
      have hlossR :
          ((bankOrdinaryBulkDonorIntegers Q).card : ℝ) ≤
            (bankOrdinarySmoothBulkDonors n Q).card +
              Nat.primeCounting B := by exact_mod_cast hloss
      dsimp only [B] at hpiSmall hlossR
      nlinarith
    have hdeltaLe : delta ≤ 3 / 100 := by
      dsimp only [delta]
      have hRone : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 100 * R)).2
      nlinarith
    have hQ0R : (0 : ℝ) ≤ Q := by exact_mod_cast hQ0
    calc
      delta * (Q : ℝ) ≤ (3 / 100 : ℝ) * (Q : ℝ) :=
        mul_le_mul_of_nonneg_right hdeltaLe hQ0R
      _ = 3 * (Q : ℝ) / 100 := by ring
      _ ≤ (bankOrdinarySmoothBulkDonors n Q).card := hsmooth
  · have hQR : Q < (R : ℚ) := lt_of_not_ge hlarge
    have hsmoothEq : bankOrdinarySmoothBulkDonors n Q =
        bankOrdinaryBulkDonorIntegers Q := by
      apply Finset.filter_eq_self.mpr
      intro u hu
      apply Nat.mem_smoothNumbers_of_lt
      · have huWindow := (mem_bankOrdinaryBulkDonorIntegers hQ0).mp hu
        have huQ : (0 : ℚ) < u := by nlinarith [huWindow.1]
        exact_mod_cast huQ
      · have huUpper := (Finset.mem_Icc.mp hu).2
        have hfloorMono : ⌊29 * Q / 20⌋₊ ≤
            ⌈29 * (R : ℚ) / 20⌉₊ := by
          have hRat : (29 * Q / 20 : ℚ) ≤
              ⌈29 * (R : ℚ) / 20⌉₊ := by
            exact (le_of_lt (by nlinarith : 29 * Q / 20 < 29 * R / 20)).trans
              (Nat.le_ceil _)
          have hfloorQ : (⌊29 * Q / 20⌋₊ : ℚ) ≤ 29 * Q / 20 :=
            Nat.floor_le (by positivity)
          exact_mod_cast hfloorQ.trans hRat
        omega
    have hcardOne : 1 ≤ (bankOrdinarySmoothBulkDonors n Q).card := by
      rw [hsmoothEq]
      exact (bankOrdinaryBulkDonorIntegers_nonempty hQ).card_pos
    have hdeltaQ : delta * (Q : ℝ) ≤ 1 := by
      dsimp only [delta]
      have hQRreal : (Q : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast hQR.le
      have hRreal : (0 : ℝ) < R := by exact_mod_cast hRpos
      calc
        1 / (100 * (R : ℝ)) * (Q : ℝ) ≤
            1 / (100 * (R : ℝ)) * (R : ℝ) := by gcongr
        _ = 1 / 100 := by field_simp [hRreal.ne']
        _ ≤ 1 := by norm_num
    exact hdeltaQ.trans (by exact_mod_cast hcardOne)

/-! ## Summing one-donor prime intervals -/









/-! ## Uniform one-donor geometry -/



















/-! ## Marker supply from the exact fiber bound -/











/-! ## The five fixed nonbottom scales -/

















end

end Erdos390.WholePaper

end

theorem solution :
∃ delta,
  And (LT.lt.{0} (0 : Real) delta)
    (∀ᶠ (n : Nat) in Filter.atTop.{0},
      ∀ (Q : Rat),
        LT.lt.{0} (20 : Rat) Q →
          LE.le.{0} Q ↑(Erdos390.Full.ArithmeticModel.yNat n) →
            LE.le.{0} (HMul.hMul.{0, 0, 0} delta ↑Q)
              ↑(Finset.card.{0} (Erdos390.WholePaper.bankOrdinarySmoothBulkDonors n Q))) := by
  exact @Erdos390.WholePaper.exists_eventually_bankOrdinarySmoothBulkDonors_lower
