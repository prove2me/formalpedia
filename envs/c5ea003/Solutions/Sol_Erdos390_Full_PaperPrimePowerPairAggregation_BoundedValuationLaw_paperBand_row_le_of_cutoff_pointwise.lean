-- Prove2me | solution 1 for Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.paperBand_row_le_of_cutoff_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:13:12.657543+00:00
-- url     : https://prove2.me/submissions/94fe112e-87f5-4433-b41e-b3df01f6837d

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Theorems.Thm_Erdos390_Full_PaperPrimePowerPairAggregation_BoundedValuationLaw_abs_covJJ_le_of_cutoff_pointwise
import Theorems.Thm_Erdos390_Lemma75_row_primePower_transfer

/- Source module: Erdos390.Full.ArithmeticModel -/
section


/-!
# Arithmetic model for the full Erdős 390 formalization

This file connects the abstract covariance columns used by the earlier audit
companion to the actual arithmetic objects in the paper.  All definitions are
total, including at `n = 0`, `m = 0`, and at non-prime bases.  The valuation
identities themselves are stated with the mathematically necessary hypotheses
that the base is prime and the sampled integer is positive.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticModel















































theorem divInd_nonneg (d m : ℕ) : 0 ≤ divInd d m := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]

theorem divInd_le_one (d m : ℕ) : divInd d m ≤ 1 := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]





















/-- A prime valuation is the finite sum of its positive-power divisibility
indicators.  The common exponent cutoff may be any `M` above the sampled
integer, hence in particular a fixed physical upper bound for a whole cell. -/
theorem valuation_eq_sum_divInd_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    valuation p m = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
  have hMpow : m ≤ p ^ M := by
    exact hmM.trans (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt))
  have hfilter := Nat.Ico_filter_pow_dvd_eq hp hm.ne' hMpow
  have hcard := Nat.factorization_eq_card_pow_dvd m hp
  calc
    valuation p m = (m.factorization p : ℝ) := rfl
    _ = (((Finset.Ico 1 m).filter fun k => p ^ k ∣ m).card : ℝ) := by
      exact_mod_cast hcard
    _ = (((Finset.Icc 1 M).filter fun k => p ^ k ∣ m).card : ℝ) := by
      rw [hfilter]
    _ = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
      simp [positiveExponents, divInd]





private theorem positiveExponents_eq_insert_high {M : ℕ} (hM : 1 ≤ M) :
    positiveExponents M = insert 1 (highExponents M) := by
  ext k
  simp only [mem_positiveExponents, Finset.mem_insert, mem_highExponents]
  omega

/-- The paper's identity `J_p = sum_{k≥2} 1_{p^k ∣ m}`, with a
common finite cutoff valid throughout a physical cell. -/
theorem higherValuation_eq_sum_high_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m = ∑ k ∈ highExponents M, divInd (p ^ k) m := by
  have hM : 1 ≤ M := hm.trans_le hmM
  rw [higherValuation, valuation_eq_sum_divInd_of_le hp hm hmM,
    positiveExponents_eq_insert_high hM]
  have h1not : 1 ∉ highExponents M := by simp
  rw [Finset.sum_insert h1not]
  simp [divInd]

theorem higherValuation_eq_sum_high {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m = ∑ k ∈ highExponents m, divInd (p ^ k) m :=
  higherValuation_eq_sum_high_of_le hp hm le_rfl











theorem higherValuation_nonneg {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    0 ≤ higherValuation p m := by
  rw [higherValuation_eq_sum_high hp hm]
  exact Finset.sum_nonneg fun k hk => divInd_nonneg (p ^ k) m

private theorem natCast_le_square (a : ℕ) : (a : ℝ) ≤ (a : ℝ) ^ 2 := by
  cases a with
  | zero => norm_num
  | succ a =>
      have h : (1 : ℝ) ≤ (a.succ : ℝ) := by exact_mod_cast a.succ_pos
      nlinarith

private theorem higherValuation_eq_natCast_pred {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m = ((m.factorization p - 1 : ℕ) : ℝ) := by
  by_cases hdvd : p ∣ m
  · have hfac : 1 ≤ m.factorization p :=
      (hp.dvd_iff_one_le_factorization hm.ne').mp hdvd
    rw [higherValuation, valuation, divInd]
    simp only [if_pos hdvd]
    rw [Nat.cast_sub hfac]
    norm_num
  · have hfac : m.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hdvd
    simp [higherValuation, valuation, divInd, hdvd, hfac]

/-- Since `J_p` is a nonnegative integer, `J_p ≤ J_p²`. -/
theorem higherValuation_le_sq {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m ≤ higherValuation p m ^ 2 := by
  rw [higherValuation_eq_natCast_pred hp hm]
  exact natCast_le_square _



end Erdos390.Full.ArithmeticModel

end

/- Source module: Erdos390.Full.PowerLedger -/
section


/-!
# Exact prime-power ledgers

The aggregate prime-power argument uses the pointwise identity
`J_p^2 = ∑_{r≥2} (2r-3) 1_{p^r∣m}`.  This file proves that identity
for the actual valuation and divisibility columns, with a common finite
physical cutoff.  Thus later expectation and covariance manipulations do not
need to treat it as a stylized fact.
-/

open scoped BigOperators

namespace Erdos390.Full.PowerLedger

open ArithmeticModel

private theorem sum_odd_Icc (a : ℕ) :
    (∑ r ∈ Finset.Icc 2 a, ((2 * r - 3 : ℕ) : ℝ)) =
      (((a - 1 : ℕ) : ℝ) ^ 2) := by
  induction a with
  | zero => simp
  | succ a ih =>
      by_cases ha : 1 ≤ a
      · rw [Finset.sum_Icc_succ_top (by omega), ih]
        have hodd : 2 * (a + 1) - 3 = 2 * a - 1 := by omega
        have h2a : 1 ≤ 2 * a := by omega
        rw [hodd, Nat.cast_sub h2a]
        norm_num [Nat.succ_eq_add_one, Nat.cast_sub ha]
        ring
      · have ha0 : a = 0 := by omega
        subst a
        norm_num

private theorem higherValuation_eq_cast_pred {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m = ((m.factorization p - 1 : ℕ) : ℝ) := by
  by_cases hdvd : p ∣ m
  · have hfac : 1 ≤ m.factorization p :=
      (hp.dvd_iff_one_le_factorization hm.ne').mp hdvd
    rw [higherValuation, valuation, divInd]
    simp only [if_pos hdvd]
    rw [Nat.cast_sub hfac]
    norm_num
  · have hfac : m.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hdvd
    simp [higherValuation, valuation, divInd, hdvd, hfac]

/-- The exact diagonal identity used in the proof of Lemma 7.5. -/
theorem higherValuation_sq_eq_weighted_sum_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m ^ 2 =
      ∑ r ∈ highExponents M,
        ((2 * r - 3 : ℕ) : ℝ) * divInd (p ^ r) m := by
  have hfacM : m.factorization p ≤ M := by
    exact (Nat.factorization_lt p hm.ne').le.trans hmM
  rw [higherValuation_eq_cast_pred hp hm]
  simp only [highExponents, divInd, hp.pow_dvd_iff_le_factorization hm.ne']
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 2 M).filter (fun r ↦ r ≤ m.factorization p) =
        Finset.Icc 2 (m.factorization p) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter, sum_odd_Icc]





end Erdos390.Full.PowerLedger

end

/- Source module: Erdos390.Full.PrimePowerCovariance -/
section


/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]

theorem expect_zero (mu : FiniteProbability Omega) :
    mu.expect (fun _ ↦ 0) = 0 := by
  simp [expect]











theorem covariance_zero_left (mu : FiniteProbability Omega) (G : Omega → ℝ) :
    mu.covariance (fun _ ↦ 0) G = 0 := by
  simp [covariance, expect]

theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]

theorem covariance_add_left (mu : FiniteProbability Omega)
    (F G H : Omega → ℝ) :
    mu.covariance (fun omega ↦ F omega + G omega) H =
      mu.covariance F H + mu.covariance G H := by
  unfold covariance
  rw [mu.expect_add F G]
  rw [show (fun omega ↦ (F omega + G omega) * H omega) =
      fun omega ↦ F omega * H omega + G omega * H omega by
    funext omega
    ring]
  rw [mu.expect_add]
  ring







theorem covariance_sum_left (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) (G : Omega → ℝ) :
    mu.covariance (fun omega ↦ ∑ i ∈ s, F i omega) G =
      ∑ i ∈ s, mu.covariance (F i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_left]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_left, ih]

theorem covariance_sum_right (mu : FiniteProbability Omega)
    (F : Omega → ℝ) (s : Finset Iota) (G : Iota → Omega → ℝ) :
    mu.covariance F (fun omega ↦ ∑ i ∈ s, G i omega) =
      ∑ i ∈ s, mu.covariance F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_right]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_right, ih]



end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel



namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}



















theorem V_eq_I_add_J (law : BoundedValuationLaw Omega M) (p : ℕ) :
    law.V p = fun omega ↦ law.I p omega + law.J p omega := by
  funext omega
  simp only [V, I, J, higherValuation]
  ring













theorem I_nonneg (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    0 ≤ law.I p omega := divInd_nonneg _ _

theorem I_le_one (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    law.I p omega ≤ 1 := divInd_le_one _ _

theorem J_nonneg (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) (omega : Omega) :
    0 ≤ law.J p omega := higherValuation_nonneg hp (law.value_pos omega)

theorem J_le_sq (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) (omega : Omega) :
    law.J p omega ≤ law.J p omega ^ 2 :=
  higherValuation_le_sq hp (law.value_pos omega)

theorem I_mul_J (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    law.I p omega * law.J p omega = law.J p omega := by
  exact divInd_mul_higherValuation p (law.value omega)



end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full

end

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

/- Source module: Erdos390.Full.LocalFugacityBounds -/
section


/-!
# Uniform bounds for restored local fugacity coefficients

The local restoration in Lemma 7.5 must retain both the factor `1 / L`
and the geometric factor `p^{-r}`.  Cardinality bounds on the exponent set
are too crude for that purpose.  This module proves the required shifted
geometric estimates directly for the actual coefficients
`exp (eta/L)^a - exp (eta/L)^(a-1)`.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityBounds

open LocalFugacity

noncomputable section

private theorem sub_injective_on_Icc (k A : ℕ) :
    Set.InjOn (fun a : ℕ ↦ a - k) (↑(Finset.Icc k A) : Set ℕ) := by
  intro a ha b hb hab
  have hka : k ≤ a := (Finset.mem_Icc.mp ha).1
  have hkb : k ≤ b := (Finset.mem_Icc.mp hb).1
  change a - k = b - k at hab
  calc
    a = (a - k) + k := (Nat.sub_add_cancel hka).symm
    _ = (b - k) + k := congrArg (fun z : ℕ ↦ z + k) hab
    _ = b := Nat.sub_add_cancel hkb





private theorem summable_linearHalfTerm : Summable linearHalfTerm := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable
      (fun i : ℕ ↦ 3 * (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two.mul_left 3
  convert hlin.add hconst using 1
  funext i
  unfold linearHalfTerm
  ring

private theorem tsum_linearHalfTerm_eq_eight :
    ∑' i : ℕ, linearHalfTerm i = 8 := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable
      (fun i : ℕ ↦ 3 * (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two.mul_left 3
  rw [show linearHalfTerm = fun i : ℕ ↦
      (i : ℝ) * (1 / (2 : ℝ)) ^ i +
        3 * (1 / (2 : ℝ)) ^ i by
    funext i
    unfold linearHalfTerm
    ring]
  rw [hlin.tsum_add hconst,
    tsum_coe_mul_geometric_of_norm_lt_one hx,
    tsum_mul_left, tsum_geometric_two]
  norm_num

/-- Shifted arithmetic--geometric tails have an absolute numerical bound.
This is the aggregate `r+1` ledger used below. -/
theorem sum_shifted_linear_half_le_eight (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
        ((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) ≤ 8 := by
  let s := Finset.Icc 2 R
  let g : ℕ → ℕ := fun r ↦ r - 2
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc 2 R
  have heq :
      (∑ r ∈ s, ((r : ℝ) + 1) *
          (1 / (2 : ℝ)) ^ (r - 2)) =
        ∑ i ∈ s.image g, linearHalfTerm i := by
    symm
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      unfold linearHalfTerm g
      norm_num only [Nat.cast_sub hr2]
      ring
    · exact hinj
  rw [heq]
  exact (summable_linearHalfTerm.sum_le_tsum (s.image g)
      (fun i hi ↦ by unfold linearHalfTerm; positivity)).trans_eq
    tsum_linearHalfTerm_eq_eight



/-- The complete finite `r+1` reciprocal-power ledger begins at `p^{-2}`
with an absolute constant. -/
theorem sum_raddone_inv_pow_le {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 R,
        ((r : ℝ) + 1) / (p : ℝ) ^ r) ≤
      8 / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        (1 / (p : ℝ) ^ 2) *
          (((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hpPow : (2 : ℝ) ^ (r - 2) ≤ (p : ℝ) ^ (r - 2) := by
        gcongr
      have hrSplit : r = 2 + (r - 2) := by omega
      have hpowSplit : (p : ℝ) ^ r =
          (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
        conv_lhs => rw [hrSplit]
        rw [pow_add]
      rw [hpowSplit]
      have hnum : 0 ≤ (r : ℝ) + 1 := by positivity
      calc
        ((r : ℝ) + 1) /
              ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2)) ≤
            ((r : ℝ) + 1) /
              ((p : ℝ) ^ 2 * (2 : ℝ) ^ (r - 2)) := by
          gcongr
        _ = (1 / (p : ℝ) ^ 2) *
            (((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ 2) *
        (∑ r ∈ Finset.Icc 2 R,
          ((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ 2) * 8 :=
      mul_le_mul_of_nonneg_left (sum_shifted_linear_half_le_eight R)
        (by positivity)
    _ = 8 / (p : ℝ) ^ 2 := by ring



private theorem summable_quadraticHalfTerm : Summable quadraticHalfTerm := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hsq : Summable
      (fun i : ℕ ↦ (i : ℝ) ^ 2 * (1 / (2 : ℝ)) ^ i) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hx
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable (fun i : ℕ ↦ (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two
  convert ((hsq.mul_left 2).add (hlin.mul_left 7)).add
    (hconst.mul_left 3) using 1
  funext i
  unfold quadraticHalfTerm
  push_cast
  ring



theorem quadraticHalfMass_nonneg : 0 ≤ quadraticHalfMass := by
  unfold quadraticHalfMass
  exact tsum_nonneg fun i ↦ by
    unfold quadraticHalfTerm
    positivity

theorem sum_shifted_quadratic_half_le_mass (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
        (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
          (1 / (2 : ℝ)) ^ (r - 2)) ≤ quadraticHalfMass := by
  let s := Finset.Icc 2 R
  let g : ℕ → ℕ := fun r ↦ r - 2
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc 2 R
  have heq :
      (∑ r ∈ s,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) =
        ∑ i ∈ s.image g, quadraticHalfTerm i := by
    symm
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hweight : 2 * r - 3 = 2 * (r - 2) + 1 := by omega
      have hshift : r + 1 = (r - 2) + 3 := by omega
      unfold quadraticHalfTerm g
      rw [hweight]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [show (r : ℝ) + 1 = ((r - 2 : ℕ) : ℝ) + 3 by
        exact_mod_cast hshift]
    · exact hinj
  rw [heq, quadraticHalfMass]
  exact summable_quadraticHalfTerm.sum_le_tsum (s.image g)
    (fun i hi ↦ by unfold quadraticHalfTerm; positivity)

/-- The exact diagonal weight `(2r-3)` still aggregates on the
`p^{-2}` scale. -/
theorem sum_diagonalWeight_raddone_inv_pow_le {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 R,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r)) ≤
      quadraticHalfMass / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        (1 / (p : ℝ) ^ 2) *
          ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hpPow : (2 : ℝ) ^ (r - 2) ≤ (p : ℝ) ^ (r - 2) := by
        gcongr
      have hrSplit : r = 2 + (r - 2) := by omega
      have hpowSplit : (p : ℝ) ^ r =
          (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
        conv_lhs => rw [hrSplit]
        rw [pow_add]
      rw [hpowSplit]
      have hweight0 : (0 : ℝ) ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
      have hnum0 : 0 ≤ (r : ℝ) + 1 := by positivity
      calc
        ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2))) ≤
            ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (2 : ℝ) ^ (r - 2))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ 2) *
            ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
              (1 / (2 : ℝ)) ^ (r - 2)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ 2) *
        (∑ r ∈ Finset.Icc 2 R,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ 2) * quadraticHalfMass :=
      mul_le_mul_of_nonneg_left (sum_shifted_quadratic_half_le_mass R)
        (by positivity)
    _ = quadraticHalfMass / (p : ℝ) ^ 2 := by ring















end

end Erdos390.Full.LocalFugacityBounds

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



/-- Every actual `p`-adic valuation in `(0,M]` is below the logarithmic
cutoff. -/
theorem factorization_le_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    m.factorization p ≤ valuationCutoff p M := by
  have hdvd : p ^ m.factorization p ∣ m :=
    (hp.pow_dvd_iff_le_factorization hm.ne').2 le_rfl
  have hpowm : p ^ m.factorization p ≤ m := Nat.le_of_dvd hm hdvd
  exact Nat.le_log_of_pow_le hp.one_lt (hpowm.trans hmM)









end

end Erdos390.Full.ValuationCutoff

end

/- Source module: Erdos390.Full.PrimePowerRowTransfer -/
section


/-!
# Actual finite-law row contraction for prime powers

The original finite contraction theorem in `Erdos390.Lemma75` is pure
finite-sum algebra, but it was stated for the audit companion's duplicate
probability structure.  This file transports that theorem definitionally to
the genuine `Full.FiniteProbability` and then specializes it to the actual
valuation columns of `BoundedValuationLaw`.

No analytic covariance estimate is asserted here.  The point is that once the
actual `JI`, `IJ`, `JJ`, diagonal, prime-sum, and endpoint bounds are proved,
their contraction to the paper's full-valuation row norm is now a theorem
about the same probability law and the same valuation functions.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerRowTransfer

noncomputable section

open Erdos390.Full
open Erdos390.Full.PrimePowerCovariance

variable {Omega Iota : Type*} [Fintype Omega]

set_option maxHeartbeats 800000







/-- The finite row contraction, now stated for the probability type used by
all actual structured-cell and exponential-tilt modules. -/
theorem row_primePower_transfer
    [DecidableEq Iota]
    (mu : Erdos390.Full.FiniteProbability Omega) (P : Finset Iota)
    (I J : Iota -> Omega -> Real) (t u rowScale : Iota -> Real)
    (C epsilon invW HT H1 H2 remRow : Real)
    (rJI rIJ rJJ : Iota -> Iota -> Real) (rD : Iota -> Real)
    (hC : 0 <= C) (hepsilon : 0 <= epsilon)
    (hinv0 : 0 <= invW) (hinv1 : invW <= 1)
    (ht0 : ∀ i ∈ P, 0 <= t i) (ht1 : ∀ i ∈ P, t i <= 1)
    (hu0 : ∀ i ∈ P, 0 <= u i) (huW : ∀ i ∈ P, u i <= invW)
    (hscale0 : ∀ i ∈ P, 0 <= rowScale i)
    (hscale : ∀ i ∈ P, rowScale i * u i = 1)
    (hI0 : ∀ i ∈ P, ∀ omega, 0 <= I i omega)
    (hI1 : ∀ i ∈ P, ∀ omega, I i omega <= 1)
    (hJ0 : ∀ i ∈ P, ∀ omega, 0 <= J i omega)
    (hJsq : ∀ i ∈ P, ∀ omega, J i omega <= J i omega ^ 2)
    (hIJpoint : ∀ i ∈ P, ∀ omega, I i omega * J i omega = J i omega)
    (hJI : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |mu.covariance (J i) (I j)| <=
        C * t i * t j * u i ^ 2 * u j +
          epsilon * u i ^ 2 * u j + rJI i j)
    (hIJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |mu.covariance (I i) (J j)| <=
        C * t i * t j * u i * u j ^ 2 +
          epsilon * u i * u j ^ 2 + rIJ i j)
    (hJJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |mu.covariance (J i) (J j)| <=
        C * t i * t j * u i ^ 2 * u j ^ 2 +
          epsilon * u i ^ 2 * u j ^ 2 + rJJ i j)
    (hMoment : ∀ i ∈ P,
      mu.expect (fun omega => J i omega ^ 2) <=
        (C + epsilon) * u i ^ 2 + rD i)
    (hTsum : (∑ j ∈ P, t j * u j) <= HT)
    (hUsum : (∑ j ∈ P, u j) <= H1)
    (hU2sum : (∑ j ∈ P, u j ^ 2) <= H2 * invW)
    (hRowRem : ∀ i ∈ P,
      rowScale i *
        ((∑ j ∈ P.erase i, (rJI i j + rIJ i j + rJJ i j)) +
          3 * rD i) <= remRow) :
    ∀ i ∈ P,
      rowScale i * ∑ j ∈ P,
        |mu.covariance (fun omega => I i omega + J i omega)
            (fun omega => I j omega + J j omega) -
          mu.covariance (I i) (I j)| <=
      C * (HT + 2 * H2 + 3) * invW +
        epsilon * (H1 + 2 * H2 + 3) * invW + remRow := by
  let muLegacy := toLegacyProbability mu
  have hJI' : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |muLegacy.covariance (J i) (I j)| <=
        C * t i * t j * u i ^ 2 * u j +
          epsilon * u i ^ 2 * u j + rJI i j := by
    simpa only [muLegacy, toLegacyProbability_covariance] using hJI
  have hIJ' : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |muLegacy.covariance (I i) (J j)| <=
        C * t i * t j * u i * u j ^ 2 +
          epsilon * u i * u j ^ 2 + rIJ i j := by
    simpa only [muLegacy, toLegacyProbability_covariance] using hIJ
  have hJJ' : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |muLegacy.covariance (J i) (J j)| <=
        C * t i * t j * u i ^ 2 * u j ^ 2 +
          epsilon * u i ^ 2 * u j ^ 2 + rJJ i j := by
    simpa only [muLegacy, toLegacyProbability_covariance] using hJJ
  have hMoment' : ∀ i ∈ P,
      muLegacy.expect (fun omega => J i omega ^ 2) <=
        (C + epsilon) * u i ^ 2 + rD i := by
    simpa only [muLegacy, toLegacyProbability_expect] using hMoment
  simpa only [muLegacy, toLegacyProbability_covariance] using
    (Erdos390.Lemma75.row_primePower_transfer
      muLegacy P I J t u rowScale C epsilon invW HT H1 H2 remRow
      rJI rIJ rJJ rD hC hepsilon hinv0 hinv1 ht0 ht1 hu0 huW
      hscale0 hscale hI0 hI1 hJ0 hJsq hIJpoint hJI' hIJ' hJJ'
      hMoment' hTsum hUsum hU2sum hRowRem)

namespace BoundedValuationLaw

variable {M : Nat} (law : BoundedValuationLaw Omega M)

/-- Specialization of the row contraction to the literal columns
`V_p = v_p(m)`, `I_p = 1_{p|m}`, and `J_p = V_p-I_p` of the actual bounded
integer-valued law. -/
theorem covVV_sub_covII_row_le
    (P : Finset Nat) (t u rowScale : Nat -> Real)
    (C epsilon invW HT H1 H2 remRow : Real)
    (rJI rIJ rJJ : Nat -> Nat -> Real) (rD : Nat -> Real)
    (hPrime : ∀ p ∈ P, p.Prime)
    (hC : 0 <= C) (hepsilon : 0 <= epsilon)
    (hinv0 : 0 <= invW) (hinv1 : invW <= 1)
    (ht0 : ∀ p ∈ P, 0 <= t p) (ht1 : ∀ p ∈ P, t p <= 1)
    (hu0 : ∀ p ∈ P, 0 <= u p) (huW : ∀ p ∈ P, u p <= invW)
    (hscale0 : ∀ p ∈ P, 0 <= rowScale p)
    (hscale : ∀ p ∈ P, rowScale p * u p = 1)
    (hJI : ∀ p ∈ P, ∀ q ∈ P.erase p,
      |law.covJI p q| <=
        C * t p * t q * u p ^ 2 * u q +
          epsilon * u p ^ 2 * u q + rJI p q)
    (hIJ : ∀ p ∈ P, ∀ q ∈ P.erase p,
      |law.covIJ p q| <=
        C * t p * t q * u p * u q ^ 2 +
          epsilon * u p * u q ^ 2 + rIJ p q)
    (hJJ : ∀ p ∈ P, ∀ q ∈ P.erase p,
      |law.covJJ p q| <=
        C * t p * t q * u p ^ 2 * u q ^ 2 +
          epsilon * u p ^ 2 * u q ^ 2 + rJJ p q)
    (hMoment : ∀ p ∈ P,
      law.probability.expect (fun omega => law.J p omega ^ 2) <=
        (C + epsilon) * u p ^ 2 + rD p)
    (hTsum : (∑ q ∈ P, t q * u q) <= HT)
    (hUsum : (∑ q ∈ P, u q) <= H1)
    (hU2sum : (∑ q ∈ P, u q ^ 2) <= H2 * invW)
    (hRowRem : ∀ p ∈ P,
      rowScale p *
        ((∑ q ∈ P.erase p, (rJI p q + rIJ p q + rJJ p q)) +
          3 * rD p) <= remRow) :
    ∀ p ∈ P,
      rowScale p * ∑ q ∈ P,
        |law.covVV p q - law.covII p q| <=
      C * (HT + 2 * H2 + 3) * invW +
        epsilon * (H1 + 2 * H2 + 3) * invW + remRow := by
  have hrow := row_primePower_transfer law.probability P law.I law.J
    t u rowScale C epsilon invW HT H1 H2 remRow rJI rIJ rJJ rD
    hC hepsilon hinv0 hinv1 ht0 ht1 hu0 huW hscale0 hscale
    (fun p hp omega => law.I_nonneg p omega)
    (fun p hp omega => law.I_le_one p omega)
    (fun p hp omega => law.J_nonneg (hPrime p hp) omega)
    (fun p hp omega => law.J_le_sq (hPrime p hp) omega)
    (fun p hp omega => law.I_mul_J p omega)
    (by simpa only [BoundedValuationLaw.covJI] using hJI)
    (by simpa only [BoundedValuationLaw.covIJ] using hIJ)
    (by simpa only [BoundedValuationLaw.covJJ] using hJJ)
    hMoment hTsum hUsum hU2sum hRowRem
  intro p hp
  have hpRow := hrow p hp
  have hfull (a b : Nat) :
      law.probability.covariance
          (fun omega => law.I a omega + law.J a omega)
          (fun omega => law.I b omega + law.J b omega) =
        law.covVV a b := by
    rw [← law.V_eq_I_add_J a, ← law.V_eq_I_add_J b]
    rfl
  simpa only [hfull, BoundedValuationLaw.covII] using hpRow

end BoundedValuationLaw

end

end Erdos390.Full.PrimePowerRowTransfer

end

/- Source module: Erdos390.Full.PaperPrimePowerRow -/
section


/-!
# The paper prime-band row contraction

This module specializes the actual finite-law contraction to

* the literal band `primeBand n W`,
* `t_p = log p / log y`,
* reciprocal weight `u_p = 1 / p`,
* row normalization `p`, and
* `invW = 1 / W`.

Thus every elementary prime-coordinate and prime-sum input in the final row
step of paper Lemma 7.5 is discharged here.  The remaining hypotheses are
exactly the actual `JI`, `IJ`, `JJ`, diagonal, and endpoint estimates proved
by the marked four-chamber analysis.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRow

open ArithmeticModel Scale PrimeSums
open PrimePowerCovariance PrimePowerRowTransfer

noncomputable section

lemma tPrime_nonneg_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    0 <= tPrime n p := by
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y (Nat.zero_lt_of_lt hn)]
    nlinarith
  have hlogp : 0 <= Real.log (p : Real) :=
    Real.log_nonneg (by exact_mod_cast (prime_of_mem_primeBand hp).one_le)
  exact div_nonneg hlogp hlogy.le

lemma tPrime_le_one_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    tPrime n p <= 1 := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y hn0]
    nlinarith
  have hpPrime := prime_of_mem_primeBand hp
  have hp0 : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
  have hyfloor : (yNat n : Real) <= y n :=
    Nat.floor_le (le_of_lt (y_pos hn0))
  have hpcast : (p : Real) <= y n := by
    exact (by exact_mod_cast le_yNat_of_mem_primeBand hp :
      (p : Real) <= (yNat n : Real)).trans hyfloor
  have hlog : Real.log (p : Real) <= Real.log (y n) :=
    Real.log_le_log hp0 hpcast
  unfold tPrime
  calc
    Real.log (p : Real) / Real.log (y n) <=
        Real.log (y n) / Real.log (y n) :=
      div_le_div_of_nonneg_right hlog hlogy.le
    _ = 1 := div_self hlogy.ne'

lemma reciprocalPrime_le_reciprocalCutoff
    {n W p : Nat} (hW : 1 < W) (hp : p ∈ primeBand n W) :
    1 / (p : Real) <= 1 / (W : Real) := by
  apply one_div_le_one_div_of_le (by exact_mod_cast Nat.zero_lt_of_lt hW)
  exact_mod_cast (cutoff_lt_of_mem_primeBand hp).le

lemma reciprocalCutoff_le_one {W : Nat} (hW : 1 < W) :
    1 / (W : Real) <= 1 := by
  have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1)
    (by exact_mod_cast hW.le : (1 : Real) <= (W : Real))
  norm_num at h ⊢
  exact h

namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : Nat}
  (law : BoundedValuationLaw Omega M)

set_option maxHeartbeats 800000

/-- Exact paper-band row contraction.  No prime-coordinate or prime-sum
hypothesis remains. -/
theorem paperBand_covVV_sub_covII_row_le
    {n W : Nat} (hn : 1 < n) (hW : 1 < W)
    (C epsilon remRow : Real)
    (rJI rIJ rJJ : Nat -> Nat -> Real) (rD : Nat -> Real)
    (hC : 0 <= C) (hepsilon : 0 <= epsilon)
    (hJI : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      |law.covJI p q| <=
        C * tPrime n p * tPrime n q *
            (1 / (p : Real)) ^ 2 * (1 / (q : Real)) +
          epsilon * (1 / (p : Real)) ^ 2 * (1 / (q : Real)) +
          rJI p q)
    (hIJ : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      |law.covIJ p q| <=
        C * tPrime n p * tPrime n q *
            (1 / (p : Real)) * (1 / (q : Real)) ^ 2 +
          epsilon * (1 / (p : Real)) * (1 / (q : Real)) ^ 2 +
          rIJ p q)
    (hJJ : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      |law.covJJ p q| <=
        C * tPrime n p * tPrime n q *
            (1 / (p : Real)) ^ 2 * (1 / (q : Real)) ^ 2 +
          epsilon * (1 / (p : Real)) ^ 2 * (1 / (q : Real)) ^ 2 +
          rJJ p q)
    (hMoment : ∀ p ∈ primeBand n W,
      law.probability.expect (fun omega => law.J p omega ^ 2) <=
        (C + epsilon) * (1 / (p : Real)) ^ 2 + rD p)
    (hRowRem : ∀ p ∈ primeBand n W,
      (p : Real) *
        ((∑ q ∈ (primeBand n W).erase p,
            (rJI p q + rIJ p q + rJJ p q)) + 3 * rD p) <= remRow) :
    ∀ p ∈ primeBand n W,
      (p : Real) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| <=
      C * (bandTReciprocalSum n W + 5) * (1 / (W : Real)) +
        epsilon * (bandReciprocalSum n W + 5) * (1 / (W : Real)) +
        remRow := by
  have hW0 : 0 <= 1 / (W : Real) := by positivity
  have hW1 : 1 / (W : Real) <= 1 := reciprocalCutoff_le_one hW
  have hSquare :
      (∑ q ∈ primeBand n W, (1 / (q : Real)) ^ 2) <=
        1 * (1 / (W : Real)) := by
    simpa only [one_mul, bandReciprocalSquareSum, one_div, inv_pow] using
      bandReciprocalSquareSum_le n W hW.le
  have hrow :=
    PrimePowerRowTransfer.BoundedValuationLaw.covVV_sub_covII_row_le law
    (primeBand n W) (tPrime n) (fun p => 1 / (p : Real))
    (fun p => (p : Real)) C epsilon (1 / (W : Real))
    (bandTReciprocalSum n W) (bandReciprocalSum n W) 1 remRow
    rJI rIJ rJJ rD
    (fun p hp => prime_of_mem_primeBand hp)
    hC hepsilon hW0 hW1
    (fun p hp => tPrime_nonneg_of_mem_primeBand hn hp)
    (fun p hp => tPrime_le_one_of_mem_primeBand hn hp)
    (fun p hp => by positivity)
    (fun p hp => reciprocalPrime_le_reciprocalCutoff hW hp)
    (fun p hp => by positivity)
    (fun p hp => by
      have hp0 : (p : Real) ≠ 0 := by
        exact_mod_cast (prime_of_mem_primeBand hp).ne_zero
      field_simp [hp0])
    hJI hIJ hJJ hMoment
    (by simp [bandTReciprocalSum, div_eq_mul_inv])
    (by rfl) hSquare hRowRem
  have hadd (x : Real) : x + 2 + 3 = x + 5 := by ring
  simpa only [mul_one, one_mul, hadd] using hrow

end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerRow

end

/- Source module: Erdos390.Full.PrimePowerCutoffCovariance -/
section


/-!
# Exact logarithmic cutoffs in the prime-power covariance expansion

`PrimePowerCovariance` expands the higher-valuation column using the common
physical endpoint.  The paper's local-factor analysis instead uses the exact
logarithmic cutoff `valuationCutoff p M`.  This file proves that the two finite
sums agree for every value in `(0,M]`, and consequently rewrites every actual
`JI`, `IJ`, `JJ`, and diagonal-moment expression at that logarithmic cutoff.

There is no asymptotic or probabilistic input here: the truncation follows
from the literal inequality

`factorization p m <= valuationCutoff p M`.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerCutoffCovariance

open ArithmeticModel PowerLedger ValuationCutoff
open FiniteProbability PrimePowerCovariance

noncomputable section

private theorem sum_divInd_high_eq_of_factorization_bounds
    {p m A B : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hA : m.factorization p ≤ A) (hB : m.factorization p ≤ B) :
    (∑ k ∈ highExponents A, divInd (p ^ k) m) =
      ∑ k ∈ highExponents B, divInd (p ^ k) m := by
  simp only [highExponents, divInd,
    hp.pow_dvd_iff_le_factorization hm.ne']
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

private theorem sum_weighted_divInd_high_eq_of_factorization_bounds
    {p m A B : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hA : m.factorization p ≤ A) (hB : m.factorization p ≤ B) :
    (∑ k ∈ highExponents A,
        (((2 * k - 3 : ℕ) : ℝ) * divInd (p ^ k) m)) =
      ∑ k ∈ highExponents B,
        (((2 * k - 3 : ℕ) : ℝ) * divInd (p ^ k) m) := by
  simp only [highExponents, divInd,
    hp.pow_dvd_iff_le_factorization hm.ne', mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Exact higher-valuation expansion at the logarithmic cutoff. -/
theorem higherValuation_eq_sum_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m =
      ∑ k ∈ highExponents (valuationCutoff p M), divInd (p ^ k) m := by
  rw [higherValuation_eq_sum_high_of_le hp hm hmM]
  exact sum_divInd_high_eq_of_factorization_bounds hp hm
    ((Nat.factorization_lt p hm.ne').le.trans hmM)
    (factorization_le_valuationCutoff hp hm hmM)

/-- Exact diagonal square ledger at the logarithmic cutoff. -/
theorem higherValuation_sq_eq_weighted_sum_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m ^ 2 =
      ∑ k ∈ highExponents (valuationCutoff p M),
        (((2 * k - 3 : ℕ) : ℝ) * divInd (p ^ k) m) := by
  rw [higherValuation_sq_eq_weighted_sum_of_le hp hm hmM]
  exact sum_weighted_divInd_high_eq_of_factorization_bounds hp hm
    ((Nat.factorization_lt p hm.ne').le.trans hmM)
    (factorization_le_valuationCutoff hp hm hmM)

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]

/-- Expectation commutes with an actual finite sum. -/
theorem expect_sum (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) :
    mu.expect (fun omega ↦ ∑ i ∈ s, F i omega) =
      ∑ i ∈ s, mu.expect (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.expect_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.expect_add, ih]

end FiniteProbability

variable {Omega : Type*} [Fintype Omega] {M : ℕ}

/-- The actual `J_p` column, cut off at `floor(log_p M)`. -/
theorem J_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    law.J p = fun omega ↦
      ∑ k ∈ highExponents (valuationCutoff p M), law.Ip p k omega := by
  funext omega
  exact higherValuation_eq_sum_valuationCutoff hp
    (law.value_pos omega) (law.value_le omega)

/-- `JI` as the literal finite sum at the exact logarithmic cutoff. -/
theorem covJI_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) (q : ℕ) :
    law.covJI p q =
      ∑ k ∈ highExponents (valuationCutoff p M),
        law.probability.covariance (law.Ip p k) (law.I q) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covJI,
    J_eq_valuationCutoff_sum law hp,
    law.probability.covariance_sum_left]

/-- `IJ` as the transposed finite sum at the exact logarithmic cutoff. -/
theorem covIJ_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) (p : ℕ) {q : ℕ} (hq : q.Prime) :
    law.covIJ p q =
      ∑ k ∈ highExponents (valuationCutoff q M),
        law.probability.covariance (law.I p) (law.Ip q k) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covIJ,
    J_eq_valuationCutoff_sum law hq,
    law.probability.covariance_sum_right]



/-- Pointwise diagonal square identity at the exact logarithmic cutoff. -/
theorem J_sq_eq_valuationCutoff_weighted_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    (fun omega ↦ law.J p omega ^ 2) = fun omega ↦
      ∑ k ∈ highExponents (valuationCutoff p M),
        (((2 * k - 3 : ℕ) : ℝ) * law.Ip p k omega) := by
  funext omega
  exact higherValuation_sq_eq_weighted_sum_valuationCutoff hp
    (law.value_pos omega) (law.value_le omega)

/-- Expected diagonal square as the exact weighted prime-power sum. -/
theorem expect_J_sq_eq_valuationCutoff_weighted_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    law.probability.expect (fun omega ↦ law.J p omega ^ 2) =
      ∑ k ∈ highExponents (valuationCutoff p M),
        (((2 * k - 3 : ℕ) : ℝ) *
          law.probability.expect (law.Ip p k)) := by
  rw [J_sq_eq_valuationCutoff_weighted_sum law hp,
    FiniteProbability.expect_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [law.probability.expect_smul]

end

end Erdos390.Full.PrimePowerCutoffCovariance

end

/- Source module: Erdos390.Full.PaperPrimePowerPairAggregation -/
section


/-!
# From actual prime-power pairs to a paper prime row

This file performs the finite aggregation that follows the pointwise
two-local estimates in Lemma 7.5.  Its inputs are covariances and moments of
the genuine divisor-indicator columns of an actual `BoundedValuationLaw`.
The preceding logarithmic-cutoff module makes every exponent range literal.

The factors `8`, `64`, and `quadraticHalfMass` are obtained from the proved
geometric series, rather than hidden in an `O`-constant.  A single universal
aggregation constant then feeds the already formalized paper-band row
contraction.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerPairAggregation

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCutoffCovariance LocalFugacityBounds
open ValuationCutoff
open PrimeSums
open PaperPrimePowerRow

noncomputable section



lemma pairAggregationConstant_nonneg : 0 ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  exact add_nonneg (by norm_num) quadraticHalfMass_nonneg

lemma eight_le_pairAggregationConstant : (8 : ℝ) ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  nlinarith [quadraticHalfMass_nonneg]

lemma sixtyFour_le_pairAggregationConstant :
    (64 : ℝ) ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  linarith [quadraticHalfMass_nonneg]

lemma quadraticHalfMass_le_pairAggregationConstant :
    quadraticHalfMass ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  norm_num

namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)

/-- A pointwise `JI` estimate contracts to the exact `p^{-2}q^{-1}` scale.
The residual remains a literal finite sum. -/
theorem abs_covJI_le_of_cutoff_pointwise
    {p q : ℕ} (hp : p.Prime) (hq0 : 0 < q)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)| ≤
        K * (((r : ℝ) + 1) /
          ((p : ℝ) ^ r * (q : ℝ))) + e r) :
    |law.covJI p q| ≤
      8 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) +
        ∑ r ∈ highExponents (valuationCutoff p M), e r := by
  rw [covJI_eq_valuationCutoff_sum law hp]
  calc
    |∑ r ∈ highExponents (valuationCutoff p M),
        law.probability.covariance (law.Ip p r) (law.I q)| ≤
        ∑ r ∈ highExponents (valuationCutoff p M),
          |law.probability.covariance (law.Ip p r) (law.I q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ highExponents (valuationCutoff p M),
          (K * (((r : ℝ) + 1) /
            ((p : ℝ) ^ r * (q : ℝ))) + e r) := by
      exact Finset.sum_le_sum fun r hr ↦ hpoint r hr
    _ = K *
          (∑ r ∈ highExponents (valuationCutoff p M),
            ((r : ℝ) + 1) / (p : ℝ) ^ r) * (1 / (q : ℝ)) +
          ∑ r ∈ highExponents (valuationCutoff p M), e r := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ K * (8 / (p : ℝ) ^ 2) * (1 / (q : ℝ)) +
          ∑ r ∈ highExponents (valuationCutoff p M), e r := by
      gcongr
      exact sum_raddone_inv_pow_le hp.two_le
    _ = 8 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) +
          ∑ r ∈ highExponents (valuationCutoff p M), e r := by
      ring

/-- The transposed one-high aggregation. -/
theorem abs_covIJ_le_of_cutoff_pointwise
    {p q : ℕ} (hp0 : 0 < p) (hq : q.Prime)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℝ)
    (hpoint : ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)| ≤
        K * (((s : ℝ) + 1) /
          ((p : ℝ) * (q : ℝ) ^ s)) + e s) :
    |law.covIJ p q| ≤
      8 * K * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 +
        ∑ s ∈ highExponents (valuationCutoff q M), e s := by
  rw [covIJ_eq_valuationCutoff_sum law p hq]
  calc
    |∑ s ∈ highExponents (valuationCutoff q M),
        law.probability.covariance (law.I p) (law.Ip q s)| ≤
        ∑ s ∈ highExponents (valuationCutoff q M),
          |law.probability.covariance (law.I p) (law.Ip q s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ highExponents (valuationCutoff q M),
          (K * (((s : ℝ) + 1) /
            ((p : ℝ) * (q : ℝ) ^ s)) + e s) := by
      exact Finset.sum_le_sum fun s hs ↦ hpoint s hs
    _ = K * (1 / (p : ℝ)) *
          (∑ s ∈ highExponents (valuationCutoff q M),
            ((s : ℝ) + 1) / (q : ℝ) ^ s) +
          ∑ s ∈ highExponents (valuationCutoff q M), e s := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ K * (1 / (p : ℝ)) * (8 / (q : ℝ) ^ 2) +
          ∑ s ∈ highExponents (valuationCutoff q M), e s := by
      gcongr
      exact sum_raddone_inv_pow_le hq.two_le
    _ = 8 * K * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 +
          ∑ s ∈ highExponents (valuationCutoff q M), e s := by
      ring



/-- The exact diagonal square ledger contracts with its literal odd weight. -/
theorem expect_J_sq_le_of_cutoff_pointwise
    {p : ℕ} (hp : p.Prime) {K : ℝ} (hK : 0 ≤ K)
    (e : ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      law.probability.expect (law.Ip p r) ≤
        K * (((r : ℝ) + 1) / (p : ℝ) ^ r) + e r) :
    law.probability.expect (fun omega ↦ law.J p omega ^ 2) ≤
      K * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
        ∑ r ∈ highExponents (valuationCutoff p M),
          (((2 * r - 3 : ℕ) : ℝ) * e r) := by
  rw [expect_J_sq_eq_valuationCutoff_weighted_sum law hp]
  calc
    (∑ r ∈ highExponents (valuationCutoff p M),
        (((2 * r - 3 : ℕ) : ℝ) *
          law.probability.expect (law.Ip p r))) ≤
        ∑ r ∈ highExponents (valuationCutoff p M),
          (((2 * r - 3 : ℕ) : ℝ) *
            (K * (((r : ℝ) + 1) / (p : ℝ) ^ r) + e r)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hpoint r hr) (by positivity)
    _ = K *
          (∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) / (p : ℝ) ^ r))) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * e r) := by
      calc
        _ = ∑ r ∈ highExponents (valuationCutoff p M),
              (K * (((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r)) +
                (((2 * r - 3 : ℕ) : ℝ) * e r)) := by
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = (∑ r ∈ highExponents (valuationCutoff p M),
              K * (((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r))) +
              ∑ r ∈ highExponents (valuationCutoff p M),
                (((2 * r - 3 : ℕ) : ℝ) * e r) :=
          Finset.sum_add_distrib
        _ = _ := by rw [Finset.mul_sum]
    _ ≤ K * (quadraticHalfMass / (p : ℝ) ^ 2) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * e r) := by
      gcongr
      exact sum_diagonalWeight_raddone_inv_pow_le hp.two_le
    _ = K * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
          ∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * e r) := by
      ring

set_option maxHeartbeats 1200000 in
/-- **Actual pointwise-to-row wiring for the paper band.**

The four pointwise hypotheses concern the genuine divisor-indicator columns
of `law` and the exact logarithmic cutoffs.  After the finite geometric
aggregation, this theorem invokes the paper-band row contraction and returns
the full-valuation covariance row required by Lemma 7.5. -/
theorem paperBand_row_le_of_cutoff_pointwise
    {n W : ℕ} (hn : 1 < n) (hW : 1 < W)
    (A epsilon remRow : ℝ)
    (eJI eIJ : ℕ → ℕ → ℕ → ℝ)
    (eJJ : ℕ → ℕ → ℕ → ℕ → ℝ)
    (eD : ℕ → ℕ → ℝ)
    (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon)
    (hJI : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)| ≤
        (A * tPrime n p * tPrime n q + epsilon) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) + eJI p q r)
    (hIJ : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)| ≤
        (A * tPrime n p * tPrime n q + epsilon) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) + eIJ p q s)
    (hJJ : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (A * tPrime n p * tPrime n q + epsilon) *
          ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s)) + eJJ p q r s)
    (hD : ∀ p ∈ primeBand n W,
      ∀ r ∈ highExponents (valuationCutoff p M),
      law.probability.expect (law.Ip p r) ≤
        (A + epsilon) * (((r : ℝ) + 1) / (p : ℝ) ^ r) + eD p r)
    (hRowRem : ∀ p ∈ primeBand n W,
      (p : ℝ) *
        ((∑ q ∈ (primeBand n W).erase p,
            ((∑ r ∈ highExponents (valuationCutoff p M), eJI p q r) +
              (∑ s ∈ highExponents (valuationCutoff q M), eIJ p q s) +
              (∑ r ∈ highExponents (valuationCutoff p M),
                ∑ s ∈ highExponents (valuationCutoff q M),
                  eJJ p q r s))) +
          3 * (∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * eD p r))) ≤ remRow) :
    ∀ p ∈ primeBand n W,
      (p : ℝ) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| ≤
      (pairAggregationConstant * A) * (bandTReciprocalSum n W + 5) *
          (1 / (W : ℝ)) +
        (pairAggregationConstant * epsilon) *
          (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) + remRow := by
  let rJI : ℕ → ℕ → ℝ := fun p q ↦
    ∑ r ∈ highExponents (valuationCutoff p M), eJI p q r
  let rIJ : ℕ → ℕ → ℝ := fun p q ↦
    ∑ s ∈ highExponents (valuationCutoff q M), eIJ p q s
  let rJJ : ℕ → ℕ → ℝ := fun p q ↦
    ∑ r ∈ highExponents (valuationCutoff p M),
      ∑ s ∈ highExponents (valuationCutoff q M), eJJ p q r s
  let rD : ℕ → ℝ := fun p ↦
    ∑ r ∈ highExponents (valuationCutoff p M),
      (((2 * r - 3 : ℕ) : ℝ) * eD p r)
  apply PaperPrimePowerRow.BoundedValuationLaw.paperBand_covVV_sub_covII_row_le
    law hn hW (pairAggregationConstant * A)
      (pairAggregationConstant * epsilon) remRow rJI rIJ rJJ rD
      (mul_nonneg pairAggregationConstant_nonneg hA)
      (mul_nonneg pairAggregationConstant_nonneg hepsilon)
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hpPrime := prime_of_mem_primeBand hpBand
    have hqPrime := prime_of_mem_primeBand hqBand
    have htp := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
    have htq := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
    let K : ℝ := A * tPrime n p * tPrime n q + epsilon
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    have hagg := abs_covJI_le_of_cutoff_pointwise law hpPrime hqPrime.pos
      hK (eJI p q) (hJI p hpBand q hqErase)
    have hcoef : 8 * K ≤ pairAggregationConstant * K :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK
    calc
      |law.covJI p q| ≤
          8 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) + rJI p q :=
        hagg
      _ ≤ pairAggregationConstant * K * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) + rJI p q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)) le_rfl
      _ = (pairAggregationConstant * A) * tPrime n p * tPrime n q *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) +
          (pairAggregationConstant * epsilon) *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) + rJI p q := by
        dsimp only [K]
        ring
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hpPrime := prime_of_mem_primeBand hpBand
    have hqPrime := prime_of_mem_primeBand hqBand
    have htp := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
    have htq := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
    let K : ℝ := A * tPrime n p * tPrime n q + epsilon
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    have hagg := abs_covIJ_le_of_cutoff_pointwise law hpPrime.pos hqPrime
      hK (eIJ p q) (hIJ p hpBand q hqErase)
    have hcoef : 8 * K ≤ pairAggregationConstant * K :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK
    calc
      |law.covIJ p q| ≤
          8 * K * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 + rIJ p q :=
        hagg
      _ ≤ pairAggregationConstant * K * (1 / (p : ℝ)) *
            (1 / (q : ℝ)) ^ 2 + rIJ p q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)) le_rfl
      _ = (pairAggregationConstant * A) * tPrime n p * tPrime n q *
            (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 +
          (pairAggregationConstant * epsilon) *
            (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 + rIJ p q := by
        dsimp only [K]
        ring
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hpPrime := prime_of_mem_primeBand hpBand
    have hqPrime := prime_of_mem_primeBand hqBand
    have htp := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
    have htq := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
    let K : ℝ := A * tPrime n p * tPrime n q + epsilon
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    have hagg := abs_covJJ_le_of_cutoff_pointwise law hpPrime hqPrime
      hK (eJJ p q) (hJJ p hpBand q hqErase)
    have hcoef : 64 * K ≤ pairAggregationConstant * K :=
      mul_le_mul_of_nonneg_right sixtyFour_le_pairAggregationConstant hK
    calc
      |law.covJJ p q| ≤
          64 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 + rJJ p q :=
        hagg
      _ ≤ pairAggregationConstant * K * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) ^ 2 + rJJ p q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)) le_rfl
      _ = (pairAggregationConstant * A) * tPrime n p * tPrime n q *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 +
          (pairAggregationConstant * epsilon) *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 + rJJ p q := by
        dsimp only [K]
        ring
  · intro p hpBand
    have hpPrime := prime_of_mem_primeBand hpBand
    have hK : 0 ≤ A + epsilon := add_nonneg hA hepsilon
    have hagg := expect_J_sq_le_of_cutoff_pointwise law hpPrime hK
      (eD p) (hD p hpBand)
    have hcoef : (A + epsilon) * quadraticHalfMass ≤
        (A + epsilon) * pairAggregationConstant :=
      mul_le_mul_of_nonneg_left quadraticHalfMass_le_pairAggregationConstant hK
    have hscale : 0 ≤ (1 / (p : ℝ)) ^ 2 := by positivity
    calc
      law.probability.expect (fun omega ↦ law.J p omega ^ 2) ≤
          (A + epsilon) * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 + rD p :=
        hagg
      _ ≤ (A + epsilon) * pairAggregationConstant *
            (1 / (p : ℝ)) ^ 2 + rD p := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hcoef hscale) le_rfl
      _ = (pairAggregationConstant * A +
            pairAggregationConstant * epsilon) *
            (1 / (p : ℝ)) ^ 2 + rD p := by ring
  · intro p hpBand
    simpa only [rJI, rIJ, rJJ, rD] using hRowRem p hpBand

end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerPairAggregation

end

universe u_1
theorem solution :
∀ {Omega : Type u_1} [inst : Fintype.{u_1} Omega] {M : Nat}
  (law : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_1} Omega M) {n W : Nat},
  LT.lt.{0} (1 : Nat) n →
    LT.lt.{0} (1 : Nat) W →
      ∀ (A epsilon remRow : Real) (eJI eIJ : Nat → Nat → Nat → Real) (eJJ : Nat → Nat → Nat → Nat → Real)
        (eD : Nat → Nat → Real),
        LE.le.{0} (0 : Real) A →
          LE.le.{0} (0 : Real) epsilon →
            (∀ (p : Nat),
                Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                  ∀ (q : Nat),
                    Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                      ∀ (r : Nat),
                        Membership.mem.{0, 0}
                            (Erdos390.Full.ArithmeticModel.highExponents
                              (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                            r →
                          LE.le.{0}
                            (abs.{0}
                              (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r)
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.I.{u_1} law q)))
                            (HAdd.hAdd.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} A (Erdos390.Full.ArithmeticModel.tPrime n p))
                                    (Erdos390.Full.ArithmeticModel.tPrime n q))
                                  epsilon)
                                (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                  (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r) ↑q)))
                              (eJI p q r))) →
              (∀ (p : Nat),
                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                    ∀ (q : Nat),
                      Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                        ∀ (s : Nat),
                          Membership.mem.{0, 0}
                              (Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.ValuationCutoff.valuationCutoff q M))
                              s →
                            LE.le.{0}
                              (abs.{0}
                                (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.I.{u_1} law p)
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law q s)))
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0}
                                  (HAdd.hAdd.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0} A (Erdos390.Full.ArithmeticModel.tPrime n p))
                                      (Erdos390.Full.ArithmeticModel.tPrime n q))
                                    epsilon)
                                  (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑s (1 : Real))
                                    (HMul.hMul.{0, 0, 0} (↑p) (HPow.hPow.{0, 0, 0} (↑q) s))))
                                (eIJ p q s))) →
                (∀ (p : Nat),
                    Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                      ∀ (q : Nat),
                        Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                          ∀ (r : Nat),
                            Membership.mem.{0, 0}
                                (Erdos390.Full.ArithmeticModel.highExponents
                                  (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                                r →
                              ∀ (s : Nat),
                                Membership.mem.{0, 0}
                                    (Erdos390.Full.ArithmeticModel.highExponents
                                      (Erdos390.Full.ValuationCutoff.valuationCutoff q M))
                                    s →
                                  LE.le.{0}
                                    (abs.{0}
                                      (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r)
                                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law q s)))
                                    (HAdd.hAdd.{0, 0, 0}
                                      (HMul.hMul.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0} A (Erdos390.Full.ArithmeticModel.tPrime n p))
                                            (Erdos390.Full.ArithmeticModel.tPrime n q))
                                          epsilon)
                                        (HDiv.hDiv.{0, 0, 0}
                                          (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                            (HAdd.hAdd.{0, 0, 0} ↑s (1 : Real)))
                                          (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r)
                                            (HPow.hPow.{0, 0, 0} (↑q) s))))
                                      (eJJ p q r s))) →
                  (∀ (p : Nat),
                      Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                        ∀ (r : Nat),
                          Membership.mem.{0, 0}
                              (Erdos390.Full.ArithmeticModel.highExponents
                                (Erdos390.Full.ValuationCutoff.valuationCutoff p M))
                              r →
                            LE.le.{0}
                              (Erdos390.Full.FiniteProbability.expect.{u_1}
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_1} law)
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{u_1} law p r))
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} A epsilon)
                                  (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real))
                                    (HPow.hPow.{0, 0, 0} (↑p) r)))
                                (eD p r))) →
                    (∀ (p : Nat),
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
                                            (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                        eJI p q r)
                                      (∑
                                        s ∈
                                          Erdos390.Full.ArithmeticModel.highExponents
                                            (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                        eIJ p q s))
                                    (∑
                                      r ∈
                                        Erdos390.Full.ArithmeticModel.highExponents
                                          (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                      ∑
                                        s ∈
                                          Erdos390.Full.ArithmeticModel.highExponents
                                            (Erdos390.Full.ValuationCutoff.valuationCutoff q M),
                                        eJJ p q r s))
                                (HMul.hMul.{0, 0, 0} (3 : Real)
                                  (∑
                                    r ∈
                                      Erdos390.Full.ArithmeticModel.highExponents
                                        (Erdos390.Full.ValuationCutoff.valuationCutoff p M),
                                    HMul.hMul.{0, 0, 0}
                                      (↑(HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) r) (3 : Nat))) (eD p r)))))
                            remRow) →
                      ∀ (p : Nat),
                        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                          LE.le.{0}
                            (HMul.hMul.{0, 0, 0} (↑p)
                              (∑ q ∈ Erdos390.Full.ArithmeticModel.primeBand n W,
                                abs.{0}
                                  (HSub.hSub.{0, 0, 0}
                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1} law p q)
                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1} law p q))))
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      Erdos390.Full.PaperPrimePowerPairAggregation.pairAggregationConstant A)
                                    (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.PrimeSums.bandTReciprocalSum n W) (5 : Real)))
                                  (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W))
                                (HMul.hMul.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      Erdos390.Full.PaperPrimePowerPairAggregation.pairAggregationConstant epsilon)
                                    (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.PrimeSums.bandReciprocalSum n W) (5 : Real)))
                                  (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑W)))
                              remRow) := by
  exact @Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.paperBand_row_le_of_cutoff_pointwise
