-- Prove2me | solution 1 for Erdos390.Full.PaperPrimePowerTailRow.eventually_tail_row_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:25:05.207914+00:00
-- url     : https://prove2.me/submissions/4cb00d37-3820-4cc0-b303-cdbb10908a67

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

/- Source module: Erdos390.Full.PrimeSums -/
section


/-!
# Prime sums on the actual moving band

This file derives the finite prime-sum estimates needed in Lemma 7.5 from
Mathlib's Chebyshev bound.  No prime-sum estimate is introduced as a contract.
-/

open scoped BigOperators Nat.Prime
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale





















private theorem inv_sq_le_telescope {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) ^ 2 ≤
      1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ k by omega)]
    norm_num
  have hrhs :
      1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) =
        1 / ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
    field_simp [hk0.ne', hk10.ne']
    nlinarith [hcast]
  rw [hrhs]
  gcongr
  nlinarith

private theorem telescope_Icc_le_inv (W Y : ℕ) (hW : 1 ≤ W) :
    (∑ k ∈ Finset.Icc (W + 1) Y,
      (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ))) ≤ 1 / (W : ℝ) := by
  by_cases hWY : W ≤ Y
  · have hset : Finset.Icc (W + 1) Y = Finset.Ico (W + 1) (Y + 1) := by
      ext k
      simp
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i ∈ Finset.range ((Y + 1) - (W + 1)),
        1 / ((((W + 1) + i) - 1 : ℕ) : ℝ) - 1 / ((W + 1 + i : ℕ) : ℝ) =
          1 / ((W + i : ℕ) : ℝ) - 1 / ((W + i + 1 : ℕ) : ℝ) := by
      intro i hi
      congr 2 <;> norm_cast <;> omega
    rw [Finset.sum_congr rfl hterm]
    have htel := Finset.sum_range_sub' (fun i : ℕ => 1 / ((W + i : ℕ) : ℝ)) (Y - W)
    rw [show (Y + 1) - (W + 1) = Y - W by omega]
    have htel' :
        (∑ i ∈ Finset.range (Y - W),
          (1 / ((W + i : ℕ) : ℝ) - 1 / ((W + i + 1 : ℕ) : ℝ))) =
            1 / ((W + 0 : ℕ) : ℝ) - 1 / ((W + (Y - W) : ℕ) : ℝ) := by
      simpa only [Nat.add_assoc] using htel
    rw [htel']
    exact sub_le_self _ (by positivity)
  · have hempty : Finset.Icc (W + 1) Y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    rw [hempty]
    simp

/-- The square-reciprocal tail needed in every `IJ/JJ` row contraction. -/
theorem bandReciprocalSquareSum_le (n W : ℕ) (hW : 1 ≤ W) :
    bandReciprocalSquareSum n W ≤ 1 / (W : ℝ) := by
  calc
    bandReciprocalSquareSum n W ≤
        ∑ p ∈ primeBand n W,
          (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_sq_le_telescope (by
        have := cutoff_lt_of_mem_primeBand hp
        omega)
    _ ≤ ∑ k ∈ Finset.Icc (W + 1) (yNat n),
          (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have h := mem_primeBand.mp hp
        simp [h.2.1, h.2.2]
      · intro k hk hnot
        have hk' := Finset.mem_Icc.mp hk
        have hk2 : 2 ≤ k := by omega
        exact le_trans (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ) ^ 2)
          (inv_sq_le_telescope hk2)
    _ ≤ 1 / (W : ℝ) := telescope_Icc_le_inv W (yNat n) hW



























end Erdos390.Full.PrimeSums

end

/- Source module: Erdos390.Full.ValuationCutoff -/
section


/-!
# The actual logarithmic valuation cutoff

The local fugacity expansion must be truncated at
`floor(log M / log p)`, not at the much larger physical endpoint `M`.
This module identifies Mathlib's `Nat.log p M` as a valid common cutoff for
all positive integers `m ≤ M`, proves the exact restored factor at that
cutoff, and compares it with the real logarithmic ratio used in the paper.
-/

namespace Erdos390.Full.ValuationCutoff

open ArithmeticModel LocalFugacityRestoration

noncomputable section









/-- The natural logarithmic cutoff is no larger than the corresponding real
logarithmic ratio. -/
theorem cast_valuationCutoff_le_log_ratio
    {p M : ℕ} (hp : 1 < p) (hM : 0 < M) :
    (valuationCutoff p M : ℝ) ≤
      Real.log (M : ℝ) / Real.log (p : ℝ) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hpowNat : p ^ valuationCutoff p M ≤ M := by
    exact Nat.pow_log_le_self p hM.ne'
  have hpowPos : (0 : ℝ) < ((p ^ valuationCutoff p M : ℕ) : ℝ) := by
    positivity
  have hpowCast : ((p ^ valuationCutoff p M : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log hpowPos hpowCast
  norm_num only [Nat.cast_pow] at hlog
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ hlogp).2
  simpa [mul_comm] using hlog



end

end Erdos390.Full.ValuationCutoff

end

/- Source module: Erdos390.Full.PaperValuationCutoff -/
section


/-!
# Paper-scale bounds for the logarithmic valuation cutoff

At the physical scale `m ≤ C n` and for `W < p ≤ n^(2/9)`, the exact local
cutoff is `O(L / log W)`.  This turns every restored coefficient tail into
`L⁻¹ p^{-r}` with an exponential constant depending on the already fixed
box and cutoff, while leaving the leading prime-power constant independent
of that box.
-/

open Filter Topology

namespace Erdos390.Full.PaperValuationCutoff

open ArithmeticModel Scale
open ValuationCutoff LocalFugacityBounds

noncomputable section

/-- The logarithmic valuation-cutoff estimate only needs a positive physical
upper endpoint.  The older `1 ≤ C` formulation below is retained as a
compatibility wrapper, but that normalization is not part of the paper's
cell hypotheses. -/
theorem eventually_valuationCutoff_div_L_le_of_pos
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        2 / Real.log (W : ℝ) := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hCevent, hInvCevent, Filter.eventually_gt_atTop 1]
    with n hCn hInvCn hn
  intro p hpBand
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hpPrime : p.Prime := prime_of_mem_primeBand hpBand
  have hpW : W < p := cutoff_lt_of_mem_primeBand hpBand
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hlogWp : Real.log (W : ℝ) ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hW.le)
    exact_mod_cast hpW.le
  have hOneMul : (1 : ℝ) ≤ C * (n : ℝ) := by
    have h := (div_le_iff₀ hC).mp hInvCn
    simpa [mul_comm] using h
  have hphysOne : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    exact_mod_cast hOneMul
  have hM : 0 < physicalBound C n := lt_of_lt_of_le Nat.zero_lt_one hphysOne
  have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
    have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
      hphysCast.trans hCnSq
    have hlog := Real.log_le_log (by exact_mod_cast hM) hleSq
    rw [Real.log_pow] at hlog
    simpa [L] using hlog
  have hlogPhys0 : 0 ≤ Real.log (physicalBound C n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hphysOne)
  have hcut := cast_valuationCutoff_le_log_ratio hpPrime.one_lt hM
  have hratio :
      Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ) ≤
        (2 * L n) / Real.log (W : ℝ) := by
    calc
      _ ≤ Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_left hlogPhys0 hlogW hlogWp
      _ ≤ (2 * L n) / Real.log (W : ℝ) :=
        div_le_div_of_nonneg_right hlogPhys hlogW.le
  calc
    (valuationCutoff p (physicalBound C n) : ℝ) / L n ≤
        (Real.log (physicalBound C n : ℝ) / Real.log (p : ℝ)) / L n :=
      div_le_div_of_nonneg_right hcut hL.le
    _ ≤ ((2 * L n) / Real.log (W : ℝ)) / L n :=
      div_le_div_of_nonneg_right hratio hL.le
    _ = 2 / Real.log (W : ℝ) := by
      field_simp [hL.ne', hlogW.ne']













end

end Erdos390.Full.PaperValuationCutoff

end

/- Source module: Erdos390.Full.PaperPrimePowerTailLedger -/
section


/-!
# Actual prime-power tail and endpoint ledgers

This module closes the finite arithmetic part of the beyond-four-mark
argument in paper Lemma 7.5.  The exponent sets are the actual logarithmic
valuation cutoffs, the primes belong to the actual finite band cut off by
`yNat`, and the four-mark boundary is the literal integer inequality
`yNat n ^ 4 < D`.  No asymptotic `O` notation is used in the statements.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailLedger

open ArithmeticModel Scale ValuationCutoff PaperValuationCutoff

noncomputable section









lemma card_highExponents_le (A : ℕ) : (highExponents A).card ≤ A := by
  simp [highExponents]

lemma card_jiBeyondFour_le (n p q A : ℕ) :
    (jiBeyondFour n p q A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)

lemma card_ijBeyondFour_le (n p q A : ℕ) :
    (ijBeyondFour n p q A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)

lemma card_jjBeyondFour_le (n p q A B : ℕ) :
    (jjBeyondFour n p q A B).card ≤ A * B := by
  calc
    (jjBeyondFour n p q A B).card ≤
        ((highExponents A).product (highExponents B)).card :=
      Finset.card_filter_le _ _
    _ = (highExponents A).card * (highExponents B).card :=
      Finset.card_product _ _
    _ ≤ A * B := Nat.mul_le_mul (card_highExponents_le A)
      (card_highExponents_le B)

lemma card_diagonalBeyondFour_le (n p A : ℕ) :
    (diagonalBeyondFour n p A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)

/-- A `JI` modulus beyond `yNat^4` has at least one full extra factor
`yNat` after its first two `p` marks. -/
lemma yNat_lt_pow_sub_two_of_jiBeyondFour
    {n p q A r : ℕ} (hr : r ∈ jiBeyondFour n p q A)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    yNat n < p ^ (r - 2) := by
  have hr2 : 2 ≤ r := (mem_highExponents.mp (Finset.mem_filter.mp hr).1).1
  have hfour : yNat n ^ 4 < p ^ r * q := (Finset.mem_filter.mp hr).2
  by_contra hnot
  have hexcess : p ^ (r - 2) ≤ yNat n := Nat.le_of_not_gt hnot
  have hp2 : p ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hpY 2
  have hfactor : p ^ r = p ^ (r - 2) * p ^ 2 := by
    calc
      p ^ r = p ^ ((r - 2) + 2) := by
        congr 1
        omega
      _ = p ^ (r - 2) * p ^ 2 := pow_add _ _ _
  have hupper : p ^ r * q ≤ yNat n ^ 4 := by
    calc
      p ^ r * q = (p ^ (r - 2) * p ^ 2) * q := by rw [hfactor]
      _ ≤ (yNat n * yNat n ^ 2) * yNat n :=
        Nat.mul_le_mul (Nat.mul_le_mul hexcess hp2) hqY
      _ = yNat n ^ 4 := by ring
  omega

/-- Transposed one-high-power excess. -/
lemma yNat_lt_pow_sub_two_of_ijBeyondFour
    {n p q A s : ℕ} (hs : s ∈ ijBeyondFour n p q A)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    yNat n < q ^ (s - 2) := by
  have hs2 : 2 ≤ s := (mem_highExponents.mp (Finset.mem_filter.mp hs).1).1
  have hfour : yNat n ^ 4 < p * q ^ s := (Finset.mem_filter.mp hs).2
  by_contra hnot
  have hexcess : q ^ (s - 2) ≤ yNat n := Nat.le_of_not_gt hnot
  have hq2 : q ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hqY 2
  have hfactor : q ^ s = q ^ 2 * q ^ (s - 2) := by
    calc
      q ^ s = q ^ (2 + (s - 2)) := by
        congr 1
        omega
      _ = q ^ 2 * q ^ (s - 2) := pow_add _ _ _
  have hupper : p * q ^ s ≤ yNat n ^ 4 := by
    calc
      p * q ^ s = p * (q ^ 2 * q ^ (s - 2)) := by rw [hfactor]
      _ ≤ yNat n * (yNat n ^ 2 * yNat n) :=
        Nat.mul_le_mul hpY (Nat.mul_le_mul hq2 hexcess)
      _ = yNat n ^ 4 := by ring
  omega

/-- Pointwise reciprocal bound for a literal `JI` tail exponent. -/
lemma jiBeyondFour_reciprocal_le
    {n p q A r : ℕ} (hr : r ∈ jiBeyondFour n p q A)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    1 / ((p : ℝ) ^ r * (q : ℝ)) ≤
      1 / ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
  have hr2 : 2 ≤ r := (mem_highExponents.mp (Finset.mem_filter.mp hr).1).1
  have hexcess := yNat_lt_pow_sub_two_of_jiBeyondFour hr hpY hqY
  have hfactor : (p : ℝ) ^ r * (q : ℝ) =
      ((p : ℝ) ^ 2 * (q : ℝ)) * (p : ℝ) ^ (r - 2) := by
    calc
      (p : ℝ) ^ r * (q : ℝ) =
          (p : ℝ) ^ (2 + (r - 2)) * (q : ℝ) := by
            congr 2
            omega
      _ = ((p : ℝ) ^ 2 * (q : ℝ)) * (p : ℝ) ^ (r - 2) := by
        rw [pow_add]
        ring
  apply one_div_le_one_div_of_le (by positivity)
  rw [hfactor]
  gcongr
  exact_mod_cast hexcess.le

/-- Pointwise reciprocal bound in the transposed orientation. -/
lemma ijBeyondFour_reciprocal_le
    {n p q A s : ℕ} (hs : s ∈ ijBeyondFour n p q A)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    1 / ((p : ℝ) * (q : ℝ) ^ s) ≤
      1 / ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
  have hs2 : 2 ≤ s := (mem_highExponents.mp (Finset.mem_filter.mp hs).1).1
  have hexcess := yNat_lt_pow_sub_two_of_ijBeyondFour hs hpY hqY
  have hfactor : (p : ℝ) * (q : ℝ) ^ s =
      ((p : ℝ) * (q : ℝ) ^ 2) * (q : ℝ) ^ (s - 2) := by
    calc
      (p : ℝ) * (q : ℝ) ^ s =
          (p : ℝ) * (q : ℝ) ^ (2 + (s - 2)) := by
            congr 2
            omega
      _ = ((p : ℝ) * (q : ℝ) ^ 2) * (q : ℝ) ^ (s - 2) := by
        rw [pow_add]
        ring
  apply one_div_le_one_div_of_le (by positivity)
  rw [hfactor]
  gcongr
  exact_mod_cast hexcess.le

/-- The complete finite `JI` reciprocal tail: the only multiplicity loss is
the actual exponent cutoff. -/
theorem sum_jiBeyondFour_reciprocal_le
    {n p q A : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    (∑ r ∈ jiBeyondFour n p q A,
        1 / ((p : ℝ) ^ r * (q : ℝ))) ≤
      (A : ℝ) /
        ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
  let K : ℝ := 1 / ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))
  calc
    (∑ r ∈ jiBeyondFour n p q A,
        1 / ((p : ℝ) ^ r * (q : ℝ))) ≤
        ∑ _r ∈ jiBeyondFour n p q A, K := by
      apply Finset.sum_le_sum
      intro r hr
      exact jiBeyondFour_reciprocal_le hr hp0 hq0 hY0 hpY hqY
    _ = ((jiBeyondFour n p q A).card : ℝ) * K := by simp
    _ ≤ (A : ℝ) * K := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_jiBeyondFour_le n p q A) (by positivity)
    _ = (A : ℝ) /
        ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
      simp [K, div_eq_mul_inv]

/-- The complete finite `IJ` reciprocal tail. -/
theorem sum_ijBeyondFour_reciprocal_le
    {n p q A : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    (∑ s ∈ ijBeyondFour n p q A,
        1 / ((p : ℝ) * (q : ℝ) ^ s)) ≤
      (A : ℝ) /
        ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
  let K : ℝ := 1 / ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))
  calc
    (∑ s ∈ ijBeyondFour n p q A,
        1 / ((p : ℝ) * (q : ℝ) ^ s)) ≤
        ∑ _s ∈ ijBeyondFour n p q A, K := by
      apply Finset.sum_le_sum
      intro s hs
      exact ijBeyondFour_reciprocal_le hs hp0 hq0 hY0 hpY hqY
    _ = ((ijBeyondFour n p q A).card : ℝ) * K := by simp
    _ ≤ (A : ℝ) * K := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_ijBeyondFour_le n p q A) (by positivity)
    _ = (A : ℝ) /
        ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
      simp [K, div_eq_mul_inv]

/-- Taking a positive cube root converts the integer inequality
`Y^2 < D^3` into the exact `Y^(2/3) < D` scale used in the paper's `JJ`
tail. -/
lemma rpow_two_thirds_lt_of_sq_lt_cube {Y D : ℕ}
    (hY0 : 0 < Y) (hD0 : 0 < D) (h : Y ^ 2 < D ^ 3) :
    (Y : ℝ) ^ (2 / 3 : ℝ) < (D : ℝ) := by
  have hcast : (Y : ℝ) ^ 2 < (D : ℝ) ^ 3 := by exact_mod_cast h
  have hr := Real.rpow_lt_rpow (show 0 ≤ (Y : ℝ) ^ 2 by positivity)
    hcast (show 0 < (1 / 3 : ℝ) by norm_num)
  have hleft : ((Y : ℝ) ^ 2) ^ (1 / 3 : ℝ) =
      (Y : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (show 0 ≤ (Y : ℝ) by positivity)]
    congr 1
    norm_num
  have hright : ((D : ℝ) ^ 3) ^ (1 / 3 : ℝ) = (D : ℝ) := by
    simpa [one_div] using Real.pow_rpow_inv_natCast
      (show 0 ≤ (D : ℝ) by positivity) (show (3 : ℕ) ≠ 0 by norm_num)
  rw [hleft, hright] at hr
  exact hr

private lemma pow_le_excess_cube {p r : ℕ} (hp0 : 0 < p) (hr3 : 3 ≤ r) :
    p ^ r ≤ (p ^ (r - 2)) ^ 3 := by
  calc
    p ^ r ≤ p ^ ((r - 2) * 3) :=
      Nat.pow_le_pow_right hp0 (by omega)
    _ = (p ^ (r - 2)) ^ 3 := pow_mul _ _ _

/-- Every literal `JJ` tail pair has excess prime-power product larger
than `yNat^(2/3)`.  The proof treats the one-high and two-high exponent
orientations separately, exactly as in the paper. -/
lemma yNat_sq_lt_excess_cube_of_jjBeyondFour
    {n p q A B r s : ℕ} (hrs : (r, s) ∈ jjBeyondFour n p q A B)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    yNat n ^ 2 < (p ^ (r - 2) * q ^ (s - 2)) ^ 3 := by
  have hrs' := Finset.mem_filter.mp hrs
  have hrmem : r ∈ highExponents A := (Finset.mem_product.mp hrs'.1).1
  have hsmem : s ∈ highExponents B := (Finset.mem_product.mp hrs'.1).2
  have hr2 : 2 ≤ r := (mem_highExponents.mp hrmem).1
  have hs2 : 2 ≤ s := (mem_highExponents.mp hsmem).1
  have hfour : yNat n ^ 4 < p ^ r * q ^ s := hrs'.2
  have hp2 : p ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hpY 2
  have hq2 : q ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hqY 2
  by_cases hrEq : r = 2
  · subst r
    have hsNe : s ≠ 2 := by
      intro hsEq
      subst s
      have hupper : p ^ 2 * q ^ 2 ≤ yNat n ^ 4 := by
        calc
          p ^ 2 * q ^ 2 ≤ yNat n ^ 2 * yNat n ^ 2 :=
            Nat.mul_le_mul hp2 hq2
          _ = yNat n ^ 4 := by ring
      omega
    have hs3 : 3 ≤ s := by omega
    have hqPow : yNat n ^ 2 < q ^ s := by
      by_contra hnot
      have hqPowLe : q ^ s ≤ yNat n ^ 2 := Nat.le_of_not_gt hnot
      have hupper : p ^ 2 * q ^ s ≤ yNat n ^ 4 := by
        calc
          p ^ 2 * q ^ s ≤ yNat n ^ 2 * yNat n ^ 2 :=
            Nat.mul_le_mul hp2 hqPowLe
          _ = yNat n ^ 4 := by ring
      omega
    have hqCube := pow_le_excess_cube hq0 hs3
    simpa using hqPow.trans_le hqCube
  · have hr3 : 3 ≤ r := by omega
    by_cases hsEq : s = 2
    · subst s
      have hpPow : yNat n ^ 2 < p ^ r := by
        by_contra hnot
        have hpPowLe : p ^ r ≤ yNat n ^ 2 := Nat.le_of_not_gt hnot
        have hupper : p ^ r * q ^ 2 ≤ yNat n ^ 4 := by
          calc
            p ^ r * q ^ 2 ≤ yNat n ^ 2 * yNat n ^ 2 :=
              Nat.mul_le_mul hpPowLe hq2
            _ = yNat n ^ 4 := by ring
        omega
      have hpCube := pow_le_excess_cube hp0 hr3
      simpa using hpPow.trans_le hpCube
    · have hs3 : 3 ≤ s := by omega
      have hpCube := pow_le_excess_cube hp0 hr3
      have hqCube := pow_le_excess_cube hq0 hs3
      have htotalCube : p ^ r * q ^ s ≤
          (p ^ (r - 2) * q ^ (s - 2)) ^ 3 := by
        calc
          p ^ r * q ^ s ≤
              (p ^ (r - 2)) ^ 3 * (q ^ (s - 2)) ^ 3 :=
            Nat.mul_le_mul hpCube hqCube
          _ = (p ^ (r - 2) * q ^ (s - 2)) ^ 3 := by ring
      have hY24 : yNat n ^ 2 ≤ yNat n ^ 4 :=
        Nat.pow_le_pow_right hY0 (by norm_num)
      exact hY24.trans_lt (hfour.trans_le htotalCube)

/-- Pointwise `JJ` reciprocal tail with the exact two-thirds power. -/
lemma jjBeyondFour_reciprocal_le
    {n p q A B r s : ℕ} (hrs : (r, s) ∈ jjBeyondFour n p q A B)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    1 / ((p : ℝ) ^ r * (q : ℝ) ^ s) ≤
      1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
        (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
  have hrs' := Finset.mem_filter.mp hrs
  have hrmem : r ∈ highExponents A := (Finset.mem_product.mp hrs'.1).1
  have hsmem : s ∈ highExponents B := (Finset.mem_product.mp hrs'.1).2
  have hr2 : 2 ≤ r := (mem_highExponents.mp hrmem).1
  have hs2 : 2 ≤ s := (mem_highExponents.mp hsmem).1
  have hexcessCube := yNat_sq_lt_excess_cube_of_jjBeyondFour
    hrs hp0 hq0 hY0 hpY hqY
  have hexcessPos : 0 < p ^ (r - 2) * q ^ (s - 2) := by positivity
  have hexcess := rpow_two_thirds_lt_of_sq_lt_cube hY0 hexcessPos hexcessCube
  have hfactor : (p : ℝ) ^ r * (q : ℝ) ^ s =
      ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) *
        ((p : ℝ) ^ (r - 2) * (q : ℝ) ^ (s - 2)) := by
    calc
      (p : ℝ) ^ r * (q : ℝ) ^ s =
          ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2)) *
            ((q : ℝ) ^ 2 * (q : ℝ) ^ (s - 2)) := by
              congr 2
              · rw [← pow_add]
                congr 1
                omega
              · rw [← pow_add]
                congr 1
                omega
      _ = ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) *
          ((p : ℝ) ^ (r - 2) * (q : ℝ) ^ (s - 2)) := by ring
  apply one_div_le_one_div_of_le (by positivity)
  rw [hfactor]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Nat.cast_mul, Nat.cast_pow] using hexcess.le

/-- The complete finite `JJ` reciprocal tail, with precisely the product of
the two actual exponent cutoffs as multiplicity. -/
theorem sum_jjBeyondFour_reciprocal_le
    {n p q A B : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    (∑ rs ∈ jjBeyondFour n p q A B,
        1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) ≤
      ((A : ℝ) * (B : ℝ)) /
        ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
          (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
  let K : ℝ := 1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
    (yNat n : ℝ) ^ (2 / 3 : ℝ))
  calc
    (∑ rs ∈ jjBeyondFour n p q A B,
        1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) ≤
        ∑ _rs ∈ jjBeyondFour n p q A B, K := by
      apply Finset.sum_le_sum
      intro rs hrs
      exact jjBeyondFour_reciprocal_le hrs hp0 hq0 hY0 hpY hqY
    _ = ((jjBeyondFour n p q A B).card : ℝ) * K := by simp
    _ ≤ ((A : ℝ) * (B : ℝ)) * K := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_jjBeyondFour_le n p q A B
    _ = ((A : ℝ) * (B : ℝ)) /
        ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
          (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
      simp [K, div_eq_mul_inv]

/-- A diagonal exponent beyond four marks has two complete extra factors
of `yNat` after the first two powers of `p`. -/
lemma yNat_sq_lt_pow_sub_two_of_diagonalBeyondFour
    {n p A r : ℕ} (hr : r ∈ diagonalBeyondFour n p A)
    (hpY : p ≤ yNat n) : yNat n ^ 2 < p ^ (r - 2) := by
  have hr2 : 2 ≤ r := (mem_highExponents.mp (Finset.mem_filter.mp hr).1).1
  have hfour : yNat n ^ 4 < p ^ r := (Finset.mem_filter.mp hr).2
  by_contra hnot
  have hexcess : p ^ (r - 2) ≤ yNat n ^ 2 := Nat.le_of_not_gt hnot
  have hp2 : p ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hpY 2
  have hfactor : p ^ r = p ^ 2 * p ^ (r - 2) := by
    calc
      p ^ r = p ^ (2 + (r - 2)) := by
        congr 1
        omega
      _ = p ^ 2 * p ^ (r - 2) := pow_add _ _ _
  have hupper : p ^ r ≤ yNat n ^ 4 := by
    calc
      p ^ r = p ^ 2 * p ^ (r - 2) := hfactor
      _ ≤ yNat n ^ 2 * yNat n ^ 2 := Nat.mul_le_mul hp2 hexcess
      _ = yNat n ^ 4 := by ring
  omega

/-- Complete diagonal reciprocal tail with the exact `(2r-3)` weight. -/
theorem sum_diagonalBeyondFour_weighted_reciprocal_le
    {n p A : ℕ} (hp0 : 0 < p) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) :
    (∑ r ∈ diagonalBeyondFour n p A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
      (2 * (A : ℝ) ^ 2) /
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
  let K : ℝ := (2 * (A : ℝ)) /
    ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)
  have hpoint (r : ℕ) (hr : r ∈ diagonalBeyondFour n p A) :
      ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r ≤ K := by
    have hrmem : r ∈ highExponents A := (Finset.mem_filter.mp hr).1
    have hr2 : 2 ≤ r := (mem_highExponents.mp hrmem).1
    have hrA : r ≤ A := (mem_highExponents.mp hrmem).2
    have hexcess := yNat_sq_lt_pow_sub_two_of_diagonalBeyondFour hr hpY
    have hfactor : (p : ℝ) ^ r =
        (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
      calc
        (p : ℝ) ^ r = (p : ℝ) ^ (2 + (r - 2)) := by
          congr 1
          omega
        _ = (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := pow_add _ _ _
    have hrecip : 1 / (p : ℝ) ^ r ≤
        1 / ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [hfactor]
      gcongr
      exact_mod_cast hexcess.le
    have hweight : ((2 * r - 3 : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by
      exact_mod_cast (show 2 * r - 3 ≤ 2 * A by omega)
    have hrecip' : ((p : ℝ) ^ r)⁻¹ ≤
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)⁻¹ := by
      simpa [one_div] using hrecip
    dsimp [K]
    rw [div_eq_mul_inv]
    exact mul_le_mul hweight hrecip' (by positivity) (by positivity)
  calc
    (∑ r ∈ diagonalBeyondFour n p A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
        ∑ _r ∈ diagonalBeyondFour n p A, K := by
      apply Finset.sum_le_sum
      intro r hr
      exact hpoint r hr
    _ = ((diagonalBeyondFour n p A).card : ℝ) * K := by simp
    _ ≤ (A : ℝ) * K := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_diagonalBeyondFour_le n p A
    _ = (2 * (A : ℝ) ^ 2) /
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
      simp [K, div_eq_mul_inv]
      ring

/-! ## Literal endpoint multiplicities -/







/-! ## Actual logarithmic cutoffs and paper-scale ledgers -/





lemma cutoffScale_pos {W : ℕ} (hW : 1 < W) : 0 < cutoffScale W := by
  unfold cutoffScale
  exact div_pos (by norm_num) (Real.log_pos (by exact_mod_cast hW))

/-- The already-proved valuation-cutoff estimate in the multiplication form
used by every finite tail and endpoint ledger below. -/
theorem eventually_actualExponentCutoff_cast_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (actualExponentCutoff C n p : ℝ) ≤ cutoffScale W * L n := by
  filter_upwards [eventually_valuationCutoff_div_L_le_of_pos C W hC hW,
    Filter.eventually_gt_atTop 1] with n hcut hn
  intro p hp
  have hL : 0 < L n := L_pos hn
  have hpCut := hcut p hp
  unfold actualExponentCutoff cutoffScale
  exact (div_le_iff₀ hL).mp hpCut

private lemma band_prime_data {n W p : ℕ} (hp : p ∈ primeBand n W) :
    0 < p ∧ 0 < yNat n ∧ p ≤ yNat n := by
  have hp0 : 0 < p := (prime_of_mem_primeBand hp).pos
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hp
  exact ⟨hp0, hp0.trans_le hpY, hpY⟩

/-- Paper-scale `JI` reciprocal tail with the actual valuation cutoff.  Its
coefficient depends on `W` but not on the tilt box. -/
theorem eventually_actual_ji_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ jiBeyondFour n p q (actualExponentCutoff C n p),
          1 / ((p : ℝ) ^ r * (q : ℝ))) ≤
        (cutoffScale W * L n) /
          ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW]
    with n hcut
  intro p hp q hq
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  rcases band_prime_data hq with ⟨hq0, _, hqY⟩
  exact (sum_jiBeyondFour_reciprocal_le hp0 hq0 hY0 hpY hqY).trans
    (div_le_div_of_nonneg_right (hcut p hp) (by positivity))

/-- Paper-scale transposed reciprocal tail. -/
theorem eventually_actual_ij_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ ijBeyondFour n p q (actualExponentCutoff C n q),
          1 / ((p : ℝ) * (q : ℝ) ^ s)) ≤
        (cutoffScale W * L n) /
          ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW]
    with n hcut
  intro p hp q hq
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  rcases band_prime_data hq with ⟨hq0, _, hqY⟩
  exact (sum_ijBeyondFour_reciprocal_le hp0 hq0 hY0 hpY hqY).trans
    (div_le_div_of_nonneg_right (hcut q hq) (by positivity))

/-- Paper-scale `JJ` reciprocal tail with the exact `yNat^(-2/3)` decay. -/
theorem eventually_actual_jj_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ rs ∈ jjBeyondFour n p q
          (actualExponentCutoff C n p) (actualExponentCutoff C n q),
          1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) ≤
        ((cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
            (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW,
    Filter.eventually_gt_atTop 1] with n hcut hn
  intro p hp q hq
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  rcases band_prime_data hq with ⟨hq0, _, hqY⟩
  have hscale0 : 0 ≤ cutoffScale W * L n :=
    mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
  have hnum :
      (actualExponentCutoff C n p : ℝ) *
          (actualExponentCutoff C n q : ℝ) ≤
        (cutoffScale W * L n) ^ 2 := by
    rw [sq]
    exact mul_le_mul (hcut p hp) (hcut q hq) (by positivity) hscale0
  exact (sum_jjBeyondFour_reciprocal_le hp0 hq0 hY0 hpY hqY).trans
    (div_le_div_of_nonneg_right hnum (by positivity))

/-- Paper-scale weighted diagonal reciprocal tail. -/
theorem eventually_actual_diagonal_weighted_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (∑ r ∈ diagonalBeyondFour n p (actualExponentCutoff C n p),
          ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
        (2 * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW]
    with n hcut
  intro p hp
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  have hscale0 : 0 ≤ cutoffScale W * L n :=
    (show 0 ≤ (actualExponentCutoff C n p : ℝ) by positivity).trans
      (hcut p hp)
  have hsq : (actualExponentCutoff C n p : ℝ) ^ 2 ≤
      (cutoffScale W * L n) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hscale0).2 (hcut p hp)
  apply (sum_diagonalBeyondFour_weighted_reciprocal_le hp0 hY0 hpY).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith







end

end Erdos390.Full.PaperPrimePowerTailLedger

end

/- Source module: Erdos390.Full.PaperPrimePowerTailRow -/
section


/-!
# The literal beyond-four residual row

The residual functions of the four pointwise displays are exactly supported
on the finite beyond-four exponent sets.  This file identifies those sums
and applies the previously proved actual-cutoff tail ledgers.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailRow

open ArithmeticModel Scale ValuationCutoff
open OmittedTiltPairChamber
open PaperPrimePowerTailLedger PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays
open PrimeSums

noncomputable section

theorem sum_eJI_eq
    (G : ℝ) (n p q A : ℕ) :
    (∑ r ∈ highExponents A, eJI G n p q r) =
      (G + G ^ 2) *
        (∑ r ∈ jiBeyondFour n p q A,
          1 / ((p : ℝ) ^ r * (q : ℝ))) := by
  unfold eJI covarianceTail jiBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [pairPower, pow_one]
  by_cases hle : p ^ r * q ≤ yNat n ^ 4
  · have hnlt : ¬ yNat n ^ 4 < p ^ r * q := Nat.not_lt_of_ge hle
    simp only [if_pos hle, if_neg hnlt]
  · have hlt : yNat n ^ 4 < p ^ r * q := Nat.lt_of_not_ge hle
    simp only [if_neg hle, if_pos hlt]
    ring

theorem sum_eIJ_eq
    (G : ℝ) (n p q A : ℕ) :
    (∑ s ∈ highExponents A, eIJ G n p q s) =
      (G + G ^ 2) *
        (∑ s ∈ ijBeyondFour n p q A,
          1 / ((p : ℝ) * (q : ℝ) ^ s)) := by
  unfold eIJ covarianceTail ijBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [pairPower, pow_one]
  by_cases hle : p * q ^ s ≤ yNat n ^ 4
  · have hnlt : ¬ yNat n ^ 4 < p * q ^ s := Nat.not_lt_of_ge hle
    simp only [if_pos hle, if_neg hnlt]
  · have hlt : yNat n ^ 4 < p * q ^ s := Nat.lt_of_not_ge hle
    simp only [if_neg hle, if_pos hlt]
    ring

theorem sum_eJJ_eq
    (G : ℝ) (n p q A B : ℕ) :
    (∑ r ∈ highExponents A, ∑ s ∈ highExponents B,
        eJJ G n p q r s) =
      (G + G ^ 2) *
        (∑ rs ∈ jjBeyondFour n p q A B,
          1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) := by
  unfold eJJ covarianceTail jjBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  calc
    (∑ r ∈ highExponents A, ∑ s ∈ highExponents B,
        if pairPower p q r s ≤ yNat n ^ 4 then 0
        else (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s)) =
      (∑ r ∈ highExponents A, ∑ s ∈ highExponents B,
        if yNat n ^ 4 < p ^ r * q ^ s then
          (G + G ^ 2) * (1 / ((p : ℝ) ^ r * (q : ℝ) ^ s)) else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      simp only [pairPower]
      by_cases hle : p ^ r * q ^ s ≤ yNat n ^ 4
      · have hnlt : ¬ yNat n ^ 4 < p ^ r * q ^ s := Nat.not_lt_of_ge hle
        simp only [if_pos hle, if_neg hnlt]
      · have hlt : yNat n ^ 4 < p ^ r * q ^ s := Nat.lt_of_not_ge hle
        simp only [if_neg hle, if_pos hlt]
        ring
    _ = ∑ rs ∈ (highExponents A).product (highExponents B),
        if yNat n ^ 4 < p ^ rs.1 * q ^ rs.2 then
          (G + G ^ 2) * (1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) else 0 := by
      symm
      exact Finset.sum_product (highExponents A) (highExponents B)
        (fun rs ↦ if yNat n ^ 4 < p ^ rs.1 * q ^ rs.2 then
          (G + G ^ 2) * (1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) else 0)

theorem sum_weighted_eD_eq
    (G : ℝ) (n p A : ℕ) :
    (∑ r ∈ highExponents A,
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) =
      G * (∑ r ∈ diagonalBeyondFour n p A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) := by
  unfold eD probabilityTail diagonalBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hle : p ^ r ≤ yNat n ^ 4
  · have hnlt : ¬ yNat n ^ 4 < p ^ r := Nat.not_lt_of_ge hle
    simp only [if_pos hle, mul_zero, if_neg hnlt]
  · have hlt : yNat n ^ 4 < p ^ r := Nat.lt_of_not_ge hle
    simp only [if_neg hle, if_pos hlt]
    ring

/-- Actual-cutoff bound for the `JI` residual sum. -/
theorem eventually_sum_eJI_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p), eJI G n p q r) ≤
        (G + G ^ 2) * ((cutoffScale W * L n) /
          ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))) := by
  filter_upwards [eventually_actual_ji_reciprocal_tail_le C W hC hW]
    with n htail
  intro p hp q hq
  rw [sum_eJI_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp q hq)
    (by nlinarith [sq_nonneg G])

/-- Actual-cutoff bound for the `IJ` residual sum. -/
theorem eventually_sum_eIJ_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ highExponents (actualExponentCutoff C n q), eIJ G n p q s) ≤
        (G + G ^ 2) * ((cutoffScale W * L n) /
          ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))) := by
  filter_upwards [eventually_actual_ij_reciprocal_tail_le C W hC hW]
    with n htail
  intro p hp q hq
  rw [sum_eIJ_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp q hq)
    (by nlinarith [sq_nonneg G])

/-- Actual-cutoff bound for the `JJ` residual sum. -/
theorem eventually_sum_eJJ_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        ∑ s ∈ highExponents (actualExponentCutoff C n q), eJJ G n p q r s) ≤
        (G + G ^ 2) * (((cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
            (yNat n : ℝ) ^ (2 / 3 : ℝ))) := by
  filter_upwards [eventually_actual_jj_reciprocal_tail_le C W hC hW]
    with n htail
  intro p hp q hq
  rw [sum_eJJ_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp q hq)
    (by nlinarith [sq_nonneg G])

/-- Actual-cutoff bound for the weighted diagonal residual sum. -/
theorem eventually_sum_weighted_eD_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) ≤
        G * ((2 * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := by
  filter_upwards [eventually_actual_diagonal_weighted_reciprocal_tail_le
    C W hC hW] with n htail
  intro p hp
  rw [sum_weighted_eD_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp) hG

/-! ## One row majorant -/





private theorem mul_div_sq_le_self {P X : ℝ}
    (hP : 1 ≤ P) (hX : 0 ≤ X) :
    P * (X / P ^ 2) ≤ X := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  calc
    P * (X / P ^ 2) = X / P := by field_simp [hP0.ne']
    _ ≤ X := div_le_self hX hP

/-- The exact four residual ledgers fit into `tailRowMajorant`, uniformly in
the selected row prime. -/
theorem eventually_tail_row_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (p : ℝ) *
        ((∑ q ∈ (primeBand n W).erase p,
            ((∑ r ∈ highExponents (actualExponentCutoff C n p),
                eJI G n p q r) +
              (∑ s ∈ highExponents (actualExponentCutoff C n q),
                eIJ G n p q s) +
              (∑ r ∈ highExponents (actualExponentCutoff C n p),
                ∑ s ∈ highExponents (actualExponentCutoff C n q),
                  eJJ G n p q r s))) +
          3 * (∑ r ∈ highExponents (actualExponentCutoff C n p),
            (((2 * r - 3 : ℕ) : ℝ) * eD G n p r))) ≤
        tailRowMajorant G W n := by
  filter_upwards [eventually_sum_eJI_le G C W hG hC hW,
    eventually_sum_eIJ_le G C W hG hC hW,
    eventually_sum_eJJ_le G C W hG hC hW,
    eventually_sum_weighted_eD_le G C W hG hC hW,
    Filter.eventually_gt_atTop 1]
    with n hJI hIJ hJJ hD hn
  intro p hpBand
  let T : ℝ := G + G ^ 2
  let K : ℝ := cutoffScale W * L n
  let Y : ℝ := yNat n
  have hpPrime := prime_of_mem_primeBand hpBand
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
  have hp0 : (0 : ℝ) ≤ p := zero_le_one.trans hp1
  have hY : 0 < Y := by
    dsimp only [Y]
    exact_mod_cast hpPrime.pos.trans_le (le_yNat_of_mem_primeBand hpBand)
  have hT : 0 ≤ T := by
    dsimp only [T]
    nlinarith [sq_nonneg G]
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (cutoffScale_pos hW).le
      (L_pos hn).le
  have hH : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hRec :
      (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ)) ≤
        bandReciprocalSum n W := by
    unfold bandReciprocalSum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (by intro q hq hnot; positivity)
  have hSqSubset :
      (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ) ^ 2) ≤
        bandReciprocalSquareSum n W := by
    unfold bandReciprocalSquareSum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (by intro q hq hnot; positivity)
  have hWcast : (1 : ℝ) ≤ W := by exact_mod_cast hW.le
  have hSq :
      (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ) ^ 2) ≤ 1 := by
    exact hSqSubset.trans ((bandReciprocalSquareSum_le n W hW.le).trans
      (div_le_self zero_le_one hWcast))
  have hJIsum :
      (∑ q ∈ (primeBand n W).erase p,
        ∑ r ∈ highExponents (actualExponentCutoff C n p),
          eJI G n p q r) ≤
        (T * K / ((p : ℝ) ^ 2 * Y)) * bandReciprocalSum n W := by
    calc
      _ ≤ ∑ q ∈ (primeBand n W).erase p,
          T * (K / ((p : ℝ) ^ 2 * (q : ℝ) * Y)) := by
        exact Finset.sum_le_sum fun q hq ↦
          hJI p hpBand q ((Finset.mem_erase.mp hq).2)
      _ = (T * K / ((p : ℝ) ^ 2 * Y)) *
          (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (T * K / ((p : ℝ) ^ 2 * Y)) *
          bandReciprocalSum n W :=
        mul_le_mul_of_nonneg_left hRec (by positivity)
  have hIJsum :
      (∑ q ∈ (primeBand n W).erase p,
        ∑ s ∈ highExponents (actualExponentCutoff C n q),
          eIJ G n p q s) ≤ T * K / ((p : ℝ) * Y) := by
    calc
      _ ≤ ∑ q ∈ (primeBand n W).erase p,
          T * (K / ((p : ℝ) * (q : ℝ) ^ 2 * Y)) := by
        exact Finset.sum_le_sum fun q hq ↦
          hIJ p hpBand q ((Finset.mem_erase.mp hq).2)
      _ = (T * K / ((p : ℝ) * Y)) *
          (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (T * K / ((p : ℝ) * Y)) * 1 :=
        mul_le_mul_of_nonneg_left hSq (by positivity)
      _ = T * K / ((p : ℝ) * Y) := by ring
  have hJJsum :
      (∑ q ∈ (primeBand n W).erase p,
        ∑ r ∈ highExponents (actualExponentCutoff C n p),
          ∑ s ∈ highExponents (actualExponentCutoff C n q),
            eJJ G n p q r s) ≤
        T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ)) := by
    calc
      _ ≤ ∑ q ∈ (primeBand n W).erase p,
          T * (K ^ 2 /
            ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ))) := by
        exact Finset.sum_le_sum fun q hq ↦
          hJJ p hpBand q ((Finset.mem_erase.mp hq).2)
      _ = (T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ))) *
          (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ))) * 1 :=
        mul_le_mul_of_nonneg_left hSq (by positivity)
      _ = T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ)) := by ring
  have hDsum :
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) ≤
        G * (2 * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ 2)) := by
    simpa only [T, K, Y] using hD p hpBand
  have hJIRow : (p : ℝ) *
      (∑ q ∈ (primeBand n W).erase p,
        ∑ r ∈ highExponents (actualExponentCutoff C n p),
          eJI G n p q r) ≤
      T * ((K / Y) * bandReciprocalSum n W) := by
    calc
      _ ≤ (p : ℝ) *
          ((T * K / ((p : ℝ) ^ 2 * Y)) * bandReciprocalSum n W) :=
        mul_le_mul_of_nonneg_left hJIsum hp0
      _ = ((p : ℝ) * ((T * K / Y) / (p : ℝ) ^ 2)) *
          bandReciprocalSum n W := by ring
      _ ≤ (T * K / Y) * bandReciprocalSum n W :=
        mul_le_mul_of_nonneg_right
          (mul_div_sq_le_self hp1 (by positivity)) hH
      _ = T * ((K / Y) * bandReciprocalSum n W) := by ring
  have hIJRow : (p : ℝ) *
      (∑ q ∈ (primeBand n W).erase p,
        ∑ s ∈ highExponents (actualExponentCutoff C n q),
          eIJ G n p q s) ≤ T * (K / Y) := by
    calc
      _ ≤ (p : ℝ) * (T * K / ((p : ℝ) * Y)) :=
        mul_le_mul_of_nonneg_left hIJsum hp0
      _ = T * (K / Y) := by field_simp [hpPrime.ne_zero]
  have hJJRow : (p : ℝ) *
      (∑ q ∈ (primeBand n W).erase p,
        ∑ r ∈ highExponents (actualExponentCutoff C n p),
          ∑ s ∈ highExponents (actualExponentCutoff C n q),
            eJJ G n p q r s) ≤ T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) := by
    calc
      _ ≤ (p : ℝ) *
          (T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hJJsum hp0
      _ = (p : ℝ) *
          ((T * K ^ 2 / Y ^ (2 / 3 : ℝ)) / (p : ℝ) ^ 2) := by ring
      _ ≤ T * K ^ 2 / Y ^ (2 / 3 : ℝ) :=
        mul_div_sq_le_self hp1 (by positivity)
      _ = T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) := by ring
  have hDRow : (p : ℝ) * 3 *
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) ≤
      6 * G * (K ^ 2 / Y ^ 2) := by
    calc
      _ ≤ (p : ℝ) * 3 *
          (G * (2 * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ 2))) :=
        mul_le_mul_of_nonneg_left hDsum (mul_nonneg hp0 (by norm_num))
      _ = 6 * G * ((p : ℝ) * ((K ^ 2 / Y ^ 2) / (p : ℝ) ^ 2)) := by
        ring
      _ ≤ 6 * G * (K ^ 2 / Y ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_div_sq_le_self hp1 (by positivity)) (by positivity)
  unfold tailRowMajorant
  dsimp only
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have htotal := add_le_add (add_le_add (add_le_add hJIRow hIJRow) hJJRow) hDRow
  dsimp only [T, K, Y] at htotal
  convert htotal using 1 <;> ring

/-! ## Vanishing of the row majorant -/















end

end Erdos390.Full.PaperPrimePowerTailRow

end

theorem solution :
∀ (G C : Real) (W : Nat),
  LE.le.{0} (0 : Real) G →
    LT.lt.{0} (0 : Real) C →
      LT.lt.{0} (1 : Nat) W →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (p : Nat),
            Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
              LE.le.{0}
                (HMul.hMul.{0, 0, 0} (↑p)
                  (HAdd.hAdd.{0, 0, 0}
                    (∑ q ∈ Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p,
                      HAdd.hAdd.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0}
                          (∑
                            r ∈
                              Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n p),
                            Erdos390.Full.PaperPrimePowerFourDisplays.eJI G n p q r)
                          (∑
                            s ∈
                              Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n q),
                            Erdos390.Full.PaperPrimePowerFourDisplays.eIJ G n p q s))
                        (∑
                          r ∈
                            Erdos390.Full.ArithmeticModel.highExponents
                              (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n p),
                          ∑
                            s ∈
                              Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n q),
                            Erdos390.Full.PaperPrimePowerFourDisplays.eJJ G n p q r s))
                    (HMul.hMul.{0, 0, 0} (3 : Real)
                      (∑
                        r ∈
                          Erdos390.Full.ArithmeticModel.highExponents
                            (Erdos390.Full.PaperPrimePowerTailLedger.actualExponentCutoff C n p),
                        HMul.hMul.{0, 0, 0} (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat)))
                          (Erdos390.Full.PaperPrimePowerFourDisplays.eD G n p r)))))
                (Erdos390.Full.PaperPrimePowerTailRow.tailRowMajorant G W n) := by
  exact @Erdos390.Full.PaperPrimePowerTailRow.eventually_tail_row_le
