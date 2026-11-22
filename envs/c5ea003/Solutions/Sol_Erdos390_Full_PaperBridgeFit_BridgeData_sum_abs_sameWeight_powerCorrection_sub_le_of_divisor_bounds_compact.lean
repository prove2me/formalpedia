-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:04:05.263452+00:00
-- url     : https://prove2.me/submissions/97019840-ccde-4cf8-91a0-b2191b54bd77

import Definitions.Def_erdos390_analytic_compact_goals
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
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_FiniteProbability_sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
import Theorems.Thm_Erdos390_Full_PrimePowerLcmGeometry_sum_highExponents_pair_inv_lcm_eq_diagonalWeight

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









end Erdos390.Full.ArithmeticModel

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

theorem covariance_comm (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G = mu.covariance G F := by
  unfold covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro omega _
    ring
  · ring

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



/-- Exact decomposition of the full-valuation covariance error. -/
theorem covVV_sub_covII (law : BoundedValuationLaw Omega M) (p q : ℕ) :
    law.covVV p q - law.covII p q =
      law.covJI p q + law.covIJ p q + law.covJJ p q := by
  rw [covVV, covII, covJI, covIJ, covJJ,
    law.V_eq_I_add_J p, law.V_eq_I_add_J q]
  rw [law.probability.covariance_add_left,
    law.probability.covariance_add_right,
    law.probability.covariance_add_right]
  ring









theorem I_nonneg (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    0 ≤ law.I p omega := divInd_nonneg _ _



theorem J_nonneg (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) (omega : Omega) :
    0 ≤ law.J p omega := higherValuation_nonneg hp (law.value_pos omega)







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

/-- Every finite shifted half-geometric tail is bounded by the complete
geometric series. -/
theorem sum_shifted_half_le_two (k A : ℕ) :
    (∑ a ∈ Finset.Icc k A,
        (1 / (2 : ℝ)) ^ (a - k)) ≤ 2 := by
  let s := Finset.Icc k A
  let g : ℕ → ℕ := fun a ↦ a - k
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc k A
  have heq :
      (∑ a ∈ s, (1 / (2 : ℝ)) ^ (a - k)) =
        ∑ i ∈ s.image g, (1 / (2 : ℝ)) ^ i := by
    symm
    rw [Finset.sum_image]
    exact hinj
  rw [heq]
  exact (summable_geometric_two.sum_le_tsum (s.image g)
    (fun i hi ↦ by positivity)).trans_eq tsum_geometric_two









/-- A finite reciprocal-power tail beginning at exponent `r+1` has the
same bound as the corresponding infinite geometric tail. -/
theorem sum_inv_pow_tail_le {p r A : ℕ} (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      2 / (p : ℝ) ^ (r + 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < (p : ℝ) := by positivity
  calc
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      ∑ a ∈ Finset.Icc (r + 1) A,
        (1 / (p : ℝ) ^ (r + 1)) *
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hra : r + 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hpPow : (2 : ℝ) ^ (a - (r + 1)) ≤
          (p : ℝ) ^ (a - (r + 1)) := by gcongr
      have haSplit : a = (r + 1) + (a - (r + 1)) := by omega
      have hpowSplit : (p : ℝ) ^ a =
          (p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1)) := by
        conv_lhs => rw [haSplit]
        rw [pow_add]
      norm_num only [Nat.cast_pow]
      rw [hpowSplit]
      calc
        1 / ((p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1))) ≤
            1 / ((p : ℝ) ^ (r + 1) *
              (2 : ℝ) ^ (a - (r + 1))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ (r + 1)) *
            (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ (r + 1)) *
        ∑ a ∈ Finset.Icc (r + 1) A,
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ (r + 1)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_shifted_half_le_two (r + 1) A)
        (by positivity)
    _ = 2 / (p : ℝ) ^ (r + 1) := by ring





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



/-- Exact higher-valuation expansion at the logarithmic cutoff. -/
theorem higherValuation_eq_sum_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m =
      ∑ k ∈ highExponents (valuationCutoff p M), divInd (p ^ k) m := by
  rw [higherValuation_eq_sum_high_of_le hp hm hmM]
  exact sum_divInd_high_eq_of_factorization_bounds hp hm
    ((Nat.factorization_lt p hm.ne').le.trans hmM)
    (factorization_le_valuationCutoff hp hm hmM)



namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]



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



/-- `JJ` as the literal double sum at the two exact logarithmic cutoffs. -/
theorem covJJ_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) :
    law.covJJ p q =
      ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          law.probability.covariance (law.Ip p k) (law.Ip q l) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covJJ,
    J_eq_valuationCutoff_sum law hp,
    J_eq_valuationCutoff_sum law hq,
    law.probability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro k _
  rw [law.probability.covariance_sum_right]





end

end Erdos390.Full.PrimePowerCutoffCovariance

end

/- Source module: Erdos390.Full.FiniteProbabilityPowerCorrectionMixturePerturbation -/
section


/-!
# Prime-power correction perturbations for tagged mixtures

The full-minus-squarefree covariance is the sum of the `JI`, `IJ`, and
`JJ` orientations.  This file packages only that exact covariance algebra.
All component first-moment and covariance-row losses remain explicit, so a
later arithmetic specialization can retain the extra reciprocal power.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Cell I : Type*} [Fintype Cell] [Fintype I]
  {Omega Theta : Cell → Type*}
  [∀ c, Fintype (Omega c)] [∀ c, Fintype (Theta c)]

/-- Componentwise perturbation budgets for the three prime-power
orientations pass through an arbitrary common tagged mixture, including all
between-component covariance terms. -/
theorem sum_abs_sigmaMixture_powerCorrectionOrientations_sub_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (nu : ∀ c, FiniteProbability (Theta c))
    (IpMu JpMu : ∀ c, Omega c → ℝ)
    (IpNu JpNu : ∀ c, Theta c → ℝ)
    (IqMu JqMu : ∀ c, I → Omega c → ℝ)
    (IqNu JqNu : ∀ c, I → Theta c → ℝ)
    {AIp AJp AIrow AJrow dIp dJp dIrow dJrow dJI dIJ dJJ : ℝ}
    (hAIp : 0 ≤ AIp) (hAJp : 0 ≤ AJp)
    (hAIrow : 0 ≤ AIrow) (hAJrow : 0 ≤ AJrow)
    (hdIp : 0 ≤ dIp) (hdJp : 0 ≤ dJp)
    (hIpBase : ∀ c, |(mu c).expect (IpMu c)| ≤ AIp)
    (hJpBase : ∀ c, |(mu c).expect (JpMu c)| ≤ AJp)
    (hIqBase : ∀ c, ∑ i, |(mu c).expect (IqMu c i)| ≤ AIrow)
    (hJqBase : ∀ c, ∑ i, |(mu c).expect (JqMu c i)| ≤ AJrow)
    (hIpDiff : ∀ c,
      |(nu c).expect (IpNu c) - (mu c).expect (IpMu c)| ≤ dIp)
    (hJpDiff : ∀ c,
      |(nu c).expect (JpNu c) - (mu c).expect (JpMu c)| ≤ dJp)
    (hIqDiff : ∀ c, ∑ i,
      |(nu c).expect (IqNu c i) - (mu c).expect (IqMu c i)| ≤ dIrow)
    (hJqDiff : ∀ c, ∑ i,
      |(nu c).expect (JqNu c i) - (mu c).expect (JqMu c i)| ≤ dJrow)
    (hJICovDiff : ∀ c, ∑ i,
      |(nu c).covariance (JpNu c) (IqNu c i) -
        (mu c).covariance (JpMu c) (IqMu c i)| ≤ dJI)
    (hIJCovDiff : ∀ c, ∑ i,
      |(nu c).covariance (IpNu c) (JqNu c i) -
        (mu c).covariance (IpMu c) (JqMu c i)| ≤ dIJ)
    (hJJCovDiff : ∀ c, ∑ i,
      |(nu c).covariance (JpNu c) (JqNu c i) -
        (mu c).covariance (JpMu c) (JqMu c i)| ≤ dJJ) :
    let Mu := sigmaMixture weight mu
    let Nu := sigmaMixture weight nu
    let IpM : Sigma Omega → ℝ := fun x ↦ IpMu x.1 x.2
    let JpM : Sigma Omega → ℝ := fun x ↦ JpMu x.1 x.2
    let IqM : I → Sigma Omega → ℝ := fun i x ↦ IqMu x.1 i x.2
    let JqM : I → Sigma Omega → ℝ := fun i x ↦ JqMu x.1 i x.2
    let IpN : Sigma Theta → ℝ := fun x ↦ IpNu x.1 x.2
    let JpN : Sigma Theta → ℝ := fun x ↦ JpNu x.1 x.2
    let IqN : I → Sigma Theta → ℝ := fun i x ↦ IqNu x.1 i x.2
    let JqN : I → Sigma Theta → ℝ := fun i x ↦ JqNu x.1 i x.2
    ∑ i,
      |((Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)))| ≤
      (dJI + 2 * ((AJp + dJp) * dIrow + AIrow * dJp)) +
      (dIJ + 2 * ((AIp + dIp) * dJrow + AJrow * dIp)) +
      (dJJ + 2 * ((AJp + dJp) * dJrow + AJrow * dJp)) := by
  dsimp only
  let Mu := sigmaMixture weight mu
  let Nu := sigmaMixture weight nu
  let IpM : Sigma Omega → ℝ := fun x ↦ IpMu x.1 x.2
  let JpM : Sigma Omega → ℝ := fun x ↦ JpMu x.1 x.2
  let IqM : I → Sigma Omega → ℝ := fun i x ↦ IqMu x.1 i x.2
  let JqM : I → Sigma Omega → ℝ := fun i x ↦ JqMu x.1 i x.2
  let IpN : Sigma Theta → ℝ := fun x ↦ IpNu x.1 x.2
  let JpN : Sigma Theta → ℝ := fun x ↦ JpNu x.1 x.2
  let IqN : I → Sigma Theta → ℝ := fun i x ↦ IqNu x.1 i x.2
  let JqN : I → Sigma Theta → ℝ := fun i x ↦ JqNu x.1 i x.2
  have hJI := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu JpMu JpNu IqMu IqNu hAJp hAIrow hdJp
    hJpBase hIqBase hJpDiff hIqDiff hJICovDiff
  have hIJ := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu IpMu IpNu JqMu JqNu hAIp hAJrow hdIp
    hIpBase hJqBase hIpDiff hJqDiff hIJCovDiff
  have hJJ := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu JpMu JpNu JqMu JqNu hAJp hAJrow hdJp
    hJpBase hJqBase hJpDiff hJqDiff hJJCovDiff
  have hpoint (i : I) :
      |((Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)))| ≤
        |Nu.covariance JpN (IqN i) - Mu.covariance JpM (IqM i)| +
        |Nu.covariance IpN (JqN i) - Mu.covariance IpM (JqM i)| +
        |Nu.covariance JpN (JqN i) - Mu.covariance JpM (JqM i)| := by
    let x := Nu.covariance JpN (IqN i) - Mu.covariance JpM (IqM i)
    let y := Nu.covariance IpN (JqN i) - Mu.covariance IpM (JqM i)
    let z := Nu.covariance JpN (JqN i) - Mu.covariance JpM (JqM i)
    have heq :
        (Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)) = x + y + z := by
      dsimp only [x, y, z]
      ring
    rw [heq]
    exact (abs_add_le (x + y) z).trans
      (add_le_add (abs_add_le x y) (le_refl _))
  calc
    ∑ i,
      |((Nu.covariance JpN (IqN i) + Nu.covariance IpN (JqN i) +
            Nu.covariance JpN (JqN i)) -
          (Mu.covariance JpM (IqM i) + Mu.covariance IpM (JqM i) +
            Mu.covariance JpM (JqM i)))| ≤
        ∑ i, (|Nu.covariance JpN (IqN i) -
              Mu.covariance JpM (IqM i)| +
            |Nu.covariance IpN (JqN i) -
              Mu.covariance IpM (JqM i)| +
            |Nu.covariance JpN (JqN i) -
              Mu.covariance JpM (JqM i)|) :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (∑ i, |Nu.covariance JpN (IqN i) -
            Mu.covariance JpM (IqM i)|) +
        (∑ i, |Nu.covariance IpN (JqN i) -
            Mu.covariance IpM (JqM i)|) +
        (∑ i, |Nu.covariance JpN (JqN i) -
            Mu.covariance JpM (JqM i)|) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (add_le_add hJI hIJ) hJJ

open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw

/-- Bounded-valuation-law specialization of the preceding tagged-mixture
identity.  The conclusion is stated directly for the literal
`(covVV-covII)` rows, so no orientation algebra is left to an application. -/
theorem sum_abs_boundedValuationSigmaMixture_powerCorrection_sub_le
    {M : ℕ}
    (weight : FiniteProbability Cell)
    (lawMu : ∀ c, BoundedValuationLaw (Omega c) M)
    (lawNu : ∀ c, BoundedValuationLaw (Theta c) M)
    (p : ℕ) (q : I → ℕ)
    {AIp AJp AIrow AJrow dIp dJp dIrow dJrow dJI dIJ dJJ : ℝ}
    (hAIp : 0 ≤ AIp) (hAJp : 0 ≤ AJp)
    (hAIrow : 0 ≤ AIrow) (hAJrow : 0 ≤ AJrow)
    (hdIp : 0 ≤ dIp) (hdJp : 0 ≤ dJp)
    (hIpBase : ∀ c,
      |(lawMu c).probability.expect ((lawMu c).I p)| ≤ AIp)
    (hJpBase : ∀ c,
      |(lawMu c).probability.expect ((lawMu c).J p)| ≤ AJp)
    (hIqBase : ∀ c, ∑ i,
      |(lawMu c).probability.expect ((lawMu c).I (q i))| ≤ AIrow)
    (hJqBase : ∀ c, ∑ i,
      |(lawMu c).probability.expect ((lawMu c).J (q i))| ≤ AJrow)
    (hIpDiff : ∀ c,
      |(lawNu c).probability.expect ((lawNu c).I p) -
        (lawMu c).probability.expect ((lawMu c).I p)| ≤ dIp)
    (hJpDiff : ∀ c,
      |(lawNu c).probability.expect ((lawNu c).J p) -
        (lawMu c).probability.expect ((lawMu c).J p)| ≤ dJp)
    (hIqDiff : ∀ c, ∑ i,
      |(lawNu c).probability.expect ((lawNu c).I (q i)) -
        (lawMu c).probability.expect ((lawMu c).I (q i))| ≤ dIrow)
    (hJqDiff : ∀ c, ∑ i,
      |(lawNu c).probability.expect ((lawNu c).J (q i)) -
        (lawMu c).probability.expect ((lawMu c).J (q i))| ≤ dJrow)
    (hJICovDiff : ∀ c, ∑ i,
      |(lawNu c).probability.covariance
          ((lawNu c).J p) ((lawNu c).I (q i)) -
        (lawMu c).probability.covariance
          ((lawMu c).J p) ((lawMu c).I (q i))| ≤ dJI)
    (hIJCovDiff : ∀ c, ∑ i,
      |(lawNu c).probability.covariance
          ((lawNu c).I p) ((lawNu c).J (q i)) -
        (lawMu c).probability.covariance
          ((lawMu c).I p) ((lawMu c).J (q i))| ≤ dIJ)
    (hJJCovDiff : ∀ c, ∑ i,
      |(lawNu c).probability.covariance
          ((lawNu c).J p) ((lawNu c).J (q i)) -
        (lawMu c).probability.covariance
          ((lawMu c).J p) ((lawMu c).J (q i))| ≤ dJJ) :
    let Mu := BoundedValuationLaw.sigmaMixture weight lawMu
    let Nu := BoundedValuationLaw.sigmaMixture weight lawNu
    ∑ i, |(Nu.covVV p (q i) - Nu.covII p (q i)) -
        (Mu.covVV p (q i) - Mu.covII p (q i))| ≤
      (dJI + 2 * ((AJp + dJp) * dIrow + AIrow * dJp)) +
      (dIJ + 2 * ((AIp + dIp) * dJrow + AJrow * dIp)) +
      (dJJ + 2 * ((AJp + dJp) * dJrow + AJrow * dJp)) := by
  dsimp only
  let Mu := BoundedValuationLaw.sigmaMixture weight lawMu
  let Nu := BoundedValuationLaw.sigmaMixture weight lawNu
  have hraw := sum_abs_sigmaMixture_powerCorrectionOrientations_sub_le
    weight (fun c ↦ (lawMu c).probability)
      (fun c ↦ (lawNu c).probability)
      (fun c ↦ (lawMu c).I p) (fun c ↦ (lawMu c).J p)
      (fun c ↦ (lawNu c).I p) (fun c ↦ (lawNu c).J p)
      (fun c i ↦ (lawMu c).I (q i))
      (fun c i ↦ (lawMu c).J (q i))
      (fun c i ↦ (lawNu c).I (q i))
      (fun c i ↦ (lawNu c).J (q i))
      hAIp hAJp hAIrow hAJrow hdIp hdJp
      hIpBase hJpBase hIqBase hJqBase hIpDiff hJpDiff
      hIqDiff hJqDiff hJICovDiff hIJCovDiff hJJCovDiff
  have hNu (i : I) :
      Nu.covVV p (q i) - Nu.covII p (q i) =
        Nu.covJI p (q i) + Nu.covIJ p (q i) + Nu.covJJ p (q i) :=
    Nu.covVV_sub_covII p (q i)
  have hMu (i : I) :
      Mu.covVV p (q i) - Mu.covII p (q i) =
        Mu.covJI p (q i) + Mu.covIJ p (q i) + Mu.covJJ p (q i) :=
    Mu.covVV_sub_covII p (q i)
  simpa only [Mu, Nu, hNu, hMu] using hraw

end

end Erdos390.Full.FiniteProbability

end

/- Source module: Erdos390.Full.PrimePowerLcmGeometry -/
section


/-!
# Diagonal prime-power lcm geometry

For the physical-tilt transfer, the diagonal `JJ` orientation contains the
joint divisibility scale `lcm(p^k,p^l)`.  The number of ordered exponent
pairs whose maximum is `r` is exactly `2r-3`.  The identities below keep
that shell multiplicity literal and then invoke the already proved
arithmetic--geometric diagonal mass.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerLcmGeometry

open ArithmeticModel LocalFugacityBounds

noncomputable section





/-- The diagonal reciprocal-lcm ledger has a fixed `p^{-2}` bound. -/
theorem sum_highExponents_pair_inv_lcm_le
    {p A : ℕ} (hp : p.Prime) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) ≤
      quadraticHalfMass / (p : ℝ) ^ 2 := by
  rw [sum_highExponents_pair_inv_lcm_eq_diagonalWeight]
  calc
    (∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
      ∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
        apply Finset.sum_le_sum
        intro r hr
        have hden : 0 ≤ (p : ℝ) ^ r := by positivity
        have hw : 0 ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
        have hr0 : 0 ≤ (r : ℝ) := by positivity
        calc
          ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r =
              ((2 * r - 3 : ℕ) : ℝ) *
                (1 / (p : ℝ) ^ r) := by ring
          _ ≤ ((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
            apply mul_le_mul_of_nonneg_left _ hw
            exact div_le_div_of_nonneg_right (by linarith) hden
    _ ≤ quadraticHalfMass / (p : ℝ) ^ 2 :=
      sum_diagonalWeight_raddone_inv_pow_le hp.two_le

/-- The corresponding product-denominator double tail factors and is
bounded by `4 p^{-4}`. -/
theorem sum_highExponents_pair_inv_product_le
    {p A : ℕ} (hp : p.Prime) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ)) ≤
      4 / (p : ℝ) ^ 4 := by
  have htail :
      (∑ k ∈ highExponents A, 1 / ((p ^ k : ℕ) : ℝ)) ≤
        2 / (p : ℝ) ^ 2 := by
    simpa only [highExponents] using
      (sum_inv_pow_tail_le (p := p) (r := 1) (A := A) hp.two_le)
  have htail0 :
      0 ≤ ∑ k ∈ highExponents A, 1 / ((p ^ k : ℕ) : ℝ) := by positivity
  calc
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ)) =
      (∑ k ∈ highExponents A, 1 / ((p ^ k : ℕ) : ℝ)) *
        (∑ l ∈ highExponents A, 1 / ((p ^ l : ℕ) : ℝ)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          norm_num only [Nat.cast_mul]
          ring
    _ ≤ (2 / (p : ℝ) ^ 2) * (2 / (p : ℝ) ^ 2) :=
      mul_le_mul htail htail htail0 (by positivity)
    _ = 4 / (p : ℝ) ^ 4 := by ring

end

end Erdos390.Full.PrimePowerLcmGeometry

end

/- Source module: Erdos390.Full.PaperBridgePhysicalPowerCorrectionRow -/
section


/-!
# The prime-power correction row through the residual physical tilt

This file keeps the actual partition-function-reweighted component weights
fixed and compares the residual physical tilt component by component.  The
high prime-power columns are summed geometrically before the tagged-mixture
covariance algebra is applied.  Consequently the final comparison is for the
literal `VV-II` row, including all between-component covariance terms.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PrimePowerCutoffCovariance ValuationCutoff LocalFugacityBounds
open PrimeSums
open PrimePowerLcmGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















private theorem expect_finset_sum
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (S : Finset ℕ)
    (f : ℕ → Omega → ℝ) :
    mu.expect (fun x ↦ ∑ k ∈ S, f k x) =
      ∑ k ∈ S, mu.expect (f k) := by
  induction S using Finset.induction_on with
  | empty => simp [FiniteProbability.expect_zero]
  | @insert k S hk ih =>
      simp only [Finset.sum_insert hk]
      rw [mu.expect_add, ih]

private theorem sum_pair_linear
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (S : Finset I) (T : Finset J)
    (a b : I → J → ℝ) (c d : ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, (c * a i j + d * b i j)) =
      c * (∑ i ∈ S, ∑ j ∈ T, a i j) +
        d * (∑ i ∈ S, ∑ j ∈ T, b i j) := by
  calc
    (∑ i ∈ S, ∑ j ∈ T, (c * a i j + d * b i j)) =
        ∑ i ∈ S,
          (c * (∑ j ∈ T, a i j) + d * (∑ j ∈ T, b i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]

private theorem sum_bandPrime_inv_eq (n W : ℕ) :
    (∑ p : BandPrime n W, 1 / (p.1 : ℝ)) =
      bandReciprocalSum n W := by
  unfold bandReciprocalSum
  simpa only using (Finset.sum_attach (primeBand n W)
    (fun p ↦ 1 / (p : ℝ)))

private theorem sum_bandPrime_inv_sq_eq (n W : ℕ) :
    (∑ p : BandPrime n W, 1 / (p.1 : ℝ) ^ 2) =
      bandReciprocalSquareSum n W := by
  unfold bandReciprocalSquareSum
  simpa only using (Finset.sum_attach (primeBand n W)
    (fun p ↦ 1 / (p : ℝ) ^ 2))

/-- A reciprocal divisor fallback geometrically sums to the natural
`p^{-2}` first-moment scale of the higher-valuation column. -/
theorem expect_J_le_of_divisor_fallback
    {Omega : Type*} [Fintype Omega] {M p : ℕ}
    (law : BoundedValuationLaw Omega M) (hp : p.Prime)
    {G : ℝ} (hG : 0 ≤ G)
    (hdiv : ∀ D : ℕ, 0 < D →
      law.probability.expect (fun x ↦ divInd D (law.value x)) ≤
        G * (1 / (D : ℝ))) :
    law.probability.expect (law.J p) ≤ 2 * G * (1 / (p : ℝ)) ^ 2 := by
  rw [J_eq_valuationCutoff_sum law hp]
  rw [expect_finset_sum]
  calc
    (∑ k ∈ highExponents (valuationCutoff p M),
        law.probability.expect (law.Ip p k)) ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          G * (1 / ((p ^ k : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [BoundedValuationLaw.Ip] using
        hdiv (p ^ k) (pow_pos hp.pos k)
    _ = G * (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ G * (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hG
      simpa only [highExponents] using
        (sum_inv_pow_tail_le (p := p) (r := 1)
          (A := valuationCutoff p M) hp.two_le)
    _ = 2 * G * (1 / (p : ℝ)) ^ 2 := by ring

/-- The same geometric summation applies to a difference of two divisor
profiles. -/
theorem abs_expect_J_sub_le_of_divisor_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {d : ℝ} (hd : 0 ≤ d)
    (hdiv : ∀ D : ℕ, 0 < D →
      |nu.probability.expect (fun x ↦ divInd D (nu.value x)) -
        mu.probability.expect (fun x ↦ divInd D (mu.value x))| ≤
          d * (1 / (D : ℝ))) :
    |nu.probability.expect (nu.J p) -
      mu.probability.expect (mu.J p)| ≤
        2 * d * (1 / (p : ℝ)) ^ 2 := by
  rw [J_eq_valuationCutoff_sum nu hp, J_eq_valuationCutoff_sum mu hp]
  rw [expect_finset_sum, expect_finset_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        (nu.probability.expect (nu.Ip p k) -
          mu.probability.expect (mu.Ip p k))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |nu.probability.expect (nu.Ip p k) -
            mu.probability.expect (mu.Ip p k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
          d * (1 / ((p ^ k : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [BoundedValuationLaw.Ip] using
        hdiv (p ^ k) (pow_pos hp.pos k)
    _ = d * (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ d * (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hd
      simpa only [highExponents] using
        (sum_inv_pow_tail_le (p := p) (r := 1)
          (A := valuationCutoff p M) hp.two_le)
    _ = 2 * d * (1 / (p : ℝ)) ^ 2 := by ring

/-- Off the diagonal, the `JI` residual-tilt covariance sums on the literal
`p^{-2}q^{-1}` scale. -/
theorem abs_covJI_sub_le_of_divisor_covariance_difference_of_ne
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p q : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJI p q - mu.covJI p q| ≤
      e * (2 * G + 6 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by
  rw [covJI_eq_valuationCutoff_sum nu hp,
    covJI_eq_valuationCutoff_sum mu hp, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        (nu.probability.covariance (nu.Ip p k) (nu.I q) -
          mu.probability.covariance (mu.Ip p k) (mu.I q))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |nu.probability.covariance (nu.Ip p k) (nu.I q) -
            mu.probability.covariance (mu.Ip p k) (mu.I q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        e * (G + 3 * G ^ 2) *
          (1 / ((p ^ k : ℕ) : ℝ)) * (1 / (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hcop : Nat.Coprime (p ^ k) (q ^ 1) :=
        Nat.coprime_pow_primes k 1 hp hq hpq
      have hlcm : Nat.lcm (p ^ k) q = p ^ k * q := by
        simpa only [pow_one] using hcop.lcm_eq_mul
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.I q) -
            mu.probability.covariance (mu.Ip p k) (mu.I q)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) q : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / (q : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip, BoundedValuationLaw.I] using
            hcov (p ^ k) q (pow_pos hp.pos k) hq.pos
        _ = e * (G + 3 * G ^ 2) *
            (1 / ((p ^ k : ℕ) : ℝ)) * (1 / (q : ℝ)) := by
          rw [hlcm, Nat.cast_mul]
          ring
    _ = (e * (G + 3 * G ^ 2) * (1 / (q : ℝ))) *
        (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (e * (G + 3 * G ^ 2) * (1 / (q : ℝ))) *
        (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [highExponents] using
          (sum_inv_pow_tail_le (p := p) (r := 1)
            (A := valuationCutoff p M) hp.two_le)
      · positivity
    _ = e * (2 * G + 6 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by ring

/-- On the diagonal, `J_p` against `I_p` retains the same `p^{-2}` scale. -/
theorem abs_covJI_sub_le_of_divisor_covariance_difference_diagonal
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJI p p - mu.covJI p p| ≤
      e * (2 * G * (1 / (p : ℝ)) ^ 2 +
        6 * G ^ 2 * (1 / (p : ℝ)) ^ 3) := by
  rw [covJI_eq_valuationCutoff_sum nu hp,
    covJI_eq_valuationCutoff_sum mu hp, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        (nu.probability.covariance (nu.Ip p k) (nu.I p) -
          mu.probability.covariance (mu.Ip p k) (mu.I p))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |nu.probability.covariance (nu.Ip p k) (nu.I p) -
            mu.probability.covariance (mu.Ip p k) (mu.I p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        e * (G * (1 / ((p ^ k : ℕ) : ℝ)) +
          3 * G ^ 2 * (1 / ((p ^ k : ℕ) : ℝ)) *
            (1 / (p : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk2 : 2 ≤ k := (mem_highExponents.mp hk).1
      have hlcm : Nat.lcm (p ^ k) p = p ^ k :=
        Nat.lcm_eq_left_iff_dvd.mpr (dvd_pow_self p (by omega))
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.I p) -
            mu.probability.covariance (mu.Ip p k) (mu.I p)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) p : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / (p : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip, BoundedValuationLaw.I] using
            hcov (p ^ k) p (pow_pos hp.pos k) hp.pos
        _ = e * (G * (1 / ((p ^ k : ℕ) : ℝ)) +
            3 * G ^ 2 * (1 / ((p ^ k : ℕ) : ℝ)) *
              (1 / (p : ℝ))) := by rw [hlcm]; ring
    _ = e * (G + 3 * G ^ 2 * (1 / (p : ℝ))) *
        (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ e * (G + 3 * G ^ 2 * (1 / (p : ℝ))) *
        (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [highExponents] using
          (sum_inv_pow_tail_le (p := p) (r := 1)
            (A := valuationCutoff p M) hp.two_le)
      · positivity
    _ = e * (2 * G * (1 / (p : ℝ)) ^ 2 +
        6 * G ^ 2 * (1 / (p : ℝ)) ^ 3) := by ring

/-- The `IJ` orientation is the transpose of the preceding `JI` estimate. -/
theorem abs_covIJ_sub_le_of_divisor_covariance_difference_of_ne
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p q : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covIJ p q - mu.covIJ p q| ≤
      e * (2 * G + 6 * G ^ 2) *
        (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := by
  have hcovSwap : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ)))) := by
    exact hcov
  have hraw := abs_covJI_sub_le_of_divisor_covariance_difference_of_ne
    nu mu hq hp hpq.symm he hG hcovSwap
  have hnu : nu.covIJ p q = nu.covJI q p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact nu.probability.covariance_comm _ _
  have hmu : mu.covIJ p q = mu.covJI q p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact mu.probability.covariance_comm _ _
  rw [hnu, hmu]
  convert hraw using 1
  ring

theorem abs_covIJ_sub_le_of_divisor_covariance_difference_diagonal
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covIJ p p - mu.covIJ p p| ≤
      e * (2 * G * (1 / (p : ℝ)) ^ 2 +
        6 * G ^ 2 * (1 / (p : ℝ)) ^ 3) := by
  have hraw := abs_covJI_sub_le_of_divisor_covariance_difference_diagonal
    nu mu hp he hG hcov
  have hnu : nu.covIJ p p = nu.covJI p p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact nu.probability.covariance_comm _ _
  have hmu : mu.covIJ p p = mu.covJI p p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact mu.probability.covariance_comm _ _
  simpa only [hnu, hmu] using hraw



/-- On the diagonal, the exact lcm shell multiplicity gives a fixed
`p^{-2}` bound; no logarithmic exponent-counting loss is introduced. -/
theorem abs_covJJ_sub_le_of_divisor_covariance_difference_diagonal
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJJ p p - mu.covJJ p p| ≤
      e * (G * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
        12 * G ^ 2 * (1 / (p : ℝ)) ^ 4) := by
  rw [covJJ_eq_valuationCutoff_sum nu hp hp,
    covJJ_eq_valuationCutoff_sum mu hp hp,
    ← Finset.sum_sub_distrib]
  let S := highExponents (valuationCutoff p M)
  calc
    |∑ k ∈ S,
        ((∑ l ∈ S, nu.probability.covariance (nu.Ip p k) (nu.Ip p l)) -
          ∑ l ∈ S,
            mu.probability.covariance (mu.Ip p k) (mu.Ip p l))| ≤
        ∑ k ∈ S,
          |∑ l ∈ S,
              nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
            ∑ l ∈ S,
              mu.probability.covariance (mu.Ip p k) (mu.Ip p l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ S,
          |∑ l ∈ S,
            (nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
              mu.probability.covariance (mu.Ip p k) (mu.Ip p l))| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ S, ∑ l ∈ S,
          |nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip p l)| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ S, ∑ l ∈ S,
        e * (G * (1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
          3 * G ^ 2 * (1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip p l)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / ((p ^ l : ℕ) : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip] using
            hcov (p ^ k) (p ^ l) (pow_pos hp.pos k) (pow_pos hp.pos l)
        _ = e * (G * (1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
            3 * G ^ 2 * (1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))) := by
          rw [Nat.cast_mul]
          ring
    _ = e * (G *
          (∑ k ∈ S, ∑ l ∈ S,
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
        3 * G ^ 2 *
          (∑ k ∈ S, ∑ l ∈ S,
            1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))) := by
      have hlin := sum_pair_linear S S
        (fun k l ↦ 1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ))
        (fun k l ↦ 1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))
        (e * G) (e * (3 * G ^ 2))
      convert hlin using 1 <;> ring
    _ ≤ e * (G * (quadraticHalfMass / (p : ℝ) ^ 2) +
        3 * G ^ 2 * (4 / (p : ℝ) ^ 4)) := by
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [S] using
              (sum_highExponents_pair_inv_lcm_le
                (p := p) (A := valuationCutoff p M) hp)) hG
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [S] using
              (sum_highExponents_pair_inv_product_le
                (p := p) (A := valuationCutoff p M) hp)) (by positivity)
      · exact he
    _ = e * (G * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
        12 * G ^ 2 * (1 / (p : ℝ)) ^ 4) := by ring

/-- The pointwise `JI` estimates aggregate over the actual prime band, with
the diagonal retained separately. -/
theorem sum_abs_covJI_sub_le_of_divisor_covariance_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M n W : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (p : BandPrime n W)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    (∑ q : BandPrime n W, |nu.covJI p.1 q.1 - mu.covJI p.1 q.1|) ≤
      e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSum n W +
        e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
          6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
  let f : BandPrime n W → ℝ := fun q ↦
    |nu.covJI p.1 q.1 - mu.covJI p.1 q.1|
  have hoff (q : BandPrime n W) (hq : q ∈
      (Finset.univ : Finset (BandPrime n W)).erase p) :
      f q ≤ e * (2 * G + 6 * G ^ 2) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) := by
    have hne : p.1 ≠ q.1 := by
      intro hpq
      exact (Finset.mem_erase.mp hq).1 (Subtype.ext hpq.symm)
    exact abs_covJI_sub_le_of_divisor_covariance_difference_of_ne
      nu mu (prime_of_mem_primeBand p.2) (prime_of_mem_primeBand q.2)
        hne he hG hcov
  have hdiag : f p ≤ e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
      6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
    exact abs_covJI_sub_le_of_divisor_covariance_difference_diagonal
      nu mu (prime_of_mem_primeBand p.2) he hG hcov
  have herase :
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
        e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSum n W := by
    calc
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
          ∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
              (1 / (q.1 : ℝ)) :=
        Finset.sum_le_sum fun q hq ↦ hoff q hq
      _ = (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            1 / (q.1 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q : BandPrime n W, 1 / (q.1 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun _ _ _ ↦ by positivity)
        · have hcoef : 0 ≤ 2 * G + 6 * G ^ 2 := by
            nlinarith [sq_nonneg G]
          positivity
      _ = _ := by rw [sum_bandPrime_inv_eq]
  change (∑ q : BandPrime n W, f q) ≤ _
  calc
    (∑ q : BandPrime n W, f q) =
        (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) +
          f p := (Finset.sum_erase_add _ _ (Finset.mem_univ p)).symm
    _ ≤ _ := add_le_add herase hdiag

/-- Transposing the same argument gives the `IJ` prime-band sum. -/
theorem sum_abs_covIJ_sub_le_of_divisor_covariance_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M n W : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (p : BandPrime n W)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    (∑ q : BandPrime n W, |nu.covIJ p.1 q.1 - mu.covIJ p.1 q.1|) ≤
      e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) *
          bandReciprocalSquareSum n W +
        e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
          6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
  let f : BandPrime n W → ℝ := fun q ↦
    |nu.covIJ p.1 q.1 - mu.covIJ p.1 q.1|
  have hoff (q : BandPrime n W) (hq : q ∈
      (Finset.univ : Finset (BandPrime n W)).erase p) :
      f q ≤ e * (2 * G + 6 * G ^ 2) *
        (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 := by
    have hne : p.1 ≠ q.1 := by
      intro hpq
      exact (Finset.mem_erase.mp hq).1 (Subtype.ext hpq.symm)
    exact abs_covIJ_sub_le_of_divisor_covariance_difference_of_ne
      nu mu (prime_of_mem_primeBand p.2) (prime_of_mem_primeBand q.2)
        hne he hG hcov
  have hdiag : f p ≤ e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
      6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
    exact abs_covIJ_sub_le_of_divisor_covariance_difference_diagonal
      nu mu (prime_of_mem_primeBand p.2) he hG hcov
  have herase :
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
        e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) *
          bandReciprocalSquareSum n W := by
    calc
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
          ∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) *
              (1 / (q.1 : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun q hq ↦ hoff q hq
      _ = (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ))) *
          (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            1 / (q.1 : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ))) *
          (∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun _ _ _ ↦ by positivity)
        · have hcoef : 0 ≤ 2 * G + 6 * G ^ 2 := by
            nlinarith [sq_nonneg G]
          positivity
      _ = _ := by rw [sum_bandPrime_inv_sq_eq]
  change (∑ q : BandPrime n W, f q) ≤ _
  calc
    (∑ q : BandPrime n W, f q) =
        (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) +
          f p := (Finset.sum_erase_add _ _ (Finset.mem_univ p)).symm
    _ ≤ _ := add_le_add herase hdiag

/-- The `JJ` prime-band sum combines the distinct-prime product tail with
the exact diagonal lcm shell ledger. -/
theorem sum_abs_covJJ_sub_le_of_divisor_covariance_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M n W : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (p : BandPrime n W)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    (∑ q : BandPrime n W, |nu.covJJ p.1 q.1 - mu.covJJ p.1 q.1|) ≤
      e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSquareSum n W +
        e * (G * quadraticHalfMass * (1 / (p.1 : ℝ)) ^ 2 +
          12 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 4) := by
  let f : BandPrime n W → ℝ := fun q ↦
    |nu.covJJ p.1 q.1 - mu.covJJ p.1 q.1|
  have hoff (q : BandPrime n W) (hq : q ∈
      (Finset.univ : Finset (BandPrime n W)).erase p) :
      f q ≤ e * (4 * G + 12 * G ^ 2) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 := by
    have hne : p.1 ≠ q.1 := by
      intro hpq
      exact (Finset.mem_erase.mp hq).1 (Subtype.ext hpq.symm)
    exact abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
      nu mu (prime_of_mem_primeBand p.2) (prime_of_mem_primeBand q.2)
        hne he hG hcov
  have hdiag : f p ≤
      e * (G * quadraticHalfMass * (1 / (p.1 : ℝ)) ^ 2 +
        12 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 4) := by
    exact abs_covJJ_sub_le_of_divisor_covariance_difference_diagonal
      nu mu (prime_of_mem_primeBand p.2) he hG hcov
  have herase :
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
        e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSquareSum n W := by
    calc
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
          ∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
              (1 / (q.1 : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun q hq ↦ hoff q hq
      _ = (e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            1 / (q.1 : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun _ _ _ ↦ by positivity)
        · have hcoef : 0 ≤ 4 * G + 12 * G ^ 2 := by
            nlinarith [sq_nonneg G]
          positivity
      _ = _ := by rw [sum_bandPrime_inv_sq_eq]
  change (∑ q : BandPrime n W, f q) ≤ _
  calc
    (∑ q : BandPrime n W, f q) =
        (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) +
          f p := (Finset.sum_erase_add _ _ (Finset.mem_univ p)).symm
    _ ≤ _ := add_le_add herase hdiag

/-- Component divisor estimates, after geometric aggregation, pass through
an arbitrary common tagged mixture.  This is the finite exact core of the
physical residual-tilt row comparison. -/
theorem sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds
    {Cell : Type*} [Fintype Cell]
    {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
    {M n W : ℕ}
    (weight : FiniteProbability Cell)
    (mu nu : ∀ c, BoundedValuationLaw (Omega c) M)
    (p : BandPrime n W)
    {epsilon G : ℝ} (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G)
    (hW : 1 < W)
    (hbase : ∀ c D, 0 < D →
      (mu c).probability.expect
          (fun x ↦ divInd D ((mu c).value x)) ≤
        G * (1 / (D : ℝ)))
    (hdiff : ∀ c D, 0 < D →
      |(nu c).probability.expect
            (fun x ↦ divInd D ((nu c).value x)) -
        (mu c).probability.expect
            (fun x ↦ divInd D ((mu c).value x))| ≤
          (8 * epsilon) * G * (1 / (D : ℝ)))
    (hcov : ∀ c D E, 0 < D → 0 < E →
      |(nu c).probability.covariance
            (fun x ↦ divInd D ((nu c).value x))
            (fun x ↦ divInd E ((nu c).value x)) -
        (mu c).probability.covariance
            (fun x ↦ divInd D ((mu c).value x))
            (fun x ↦ divInd E ((mu c).value x))| ≤
        (8 * epsilon) *
          (G * (1 / (Nat.lcm D E : ℝ)) +
            3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    let Mu := sigmaMixture weight mu
    let Nu := sigmaMixture weight nu
    (∑ q : BandPrime n W,
      |(Nu.covVV p.1 q.1 - Nu.covII p.1 q.1) -
        (Mu.covVV p.1 q.1 - Mu.covII p.1 q.1)|) ≤
      physicalPowerCorrectionMixtureBudget epsilon G n W p.1 := by
  dsimp only
  let e : ℝ := 8 * epsilon
  let H : ℝ := bandReciprocalSum n W
  let S₂ : ℝ := bandReciprocalSquareSum n W
  let w₁ : ℝ := 1 / (W : ℝ)
  let p₁ : ℝ := 1 / (p.1 : ℝ)
  let AIp := G * p₁
  let AJp := 2 * G * p₁ ^ 2
  let AIrow := G * H
  let AJrow := 2 * G * w₁
  let dIp := e * G * p₁
  let dJp := 2 * e * G * p₁ ^ 2
  let dIrow := e * G * H
  let dJrow := 2 * e * G * w₁
  let dJI := e * (2 * G + 6 * G ^ 2) * p₁ ^ 2 * H +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dIJ := e * (2 * G + 6 * G ^ 2) * p₁ * S₂ +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dJJ := e * (4 * G + 12 * G ^ 2) * p₁ ^ 2 * S₂ +
    e * (G * quadraticHalfMass * p₁ ^ 2 + 12 * G ^ 2 * p₁ ^ 4)
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hH : 0 ≤ H := by dsimp only [H, bandReciprocalSum]; positivity
  have hS₂ : 0 ≤ S₂ := by
    dsimp only [S₂, bandReciprocalSquareSum]
    positivity
  have hw₁ : 0 ≤ w₁ := by dsimp only [w₁]; positivity
  have hp₁ : 0 ≤ p₁ := by dsimp only [p₁]; positivity
  have hAIp : 0 ≤ AIp := by dsimp only [AIp]; positivity
  have hAJp : 0 ≤ AJp := by dsimp only [AJp]; positivity
  have hAIrow : 0 ≤ AIrow := by dsimp only [AIrow]; positivity
  have hAJrow : 0 ≤ AJrow := by dsimp only [AJrow]; positivity
  have hdIp0 : 0 ≤ dIp := by dsimp only [dIp]; positivity
  have hdJp0 : 0 ≤ dJp := by dsimp only [dJp]; positivity
  have hIpBase (c : Cell) :
      |(mu c).probability.expect ((mu c).I p.1)| ≤ AIp := by
    have hnonneg := (mu c).probability.expect_nonneg ((mu c).I p.1)
      ((mu c).I_nonneg p.1)
    rw [abs_of_nonneg hnonneg]
    simpa only [BoundedValuationLaw.I, AIp, p₁, mul_assoc] using
      hbase c p.1 (prime_of_mem_primeBand p.2).pos
  have hJpBase (c : Cell) :
      |(mu c).probability.expect ((mu c).J p.1)| ≤ AJp := by
    have hpPrime := prime_of_mem_primeBand p.2
    have hnonneg := (mu c).probability.expect_nonneg ((mu c).J p.1)
      ((mu c).J_nonneg hpPrime)
    rw [abs_of_nonneg hnonneg]
    simpa only [AJp, p₁] using
      expect_J_le_of_divisor_fallback (mu c) hpPrime hG (hbase c)
  have hIqBase (c : Cell) :
      (∑ q : BandPrime n W,
        |(mu c).probability.expect ((mu c).I q.1)|) ≤ AIrow := by
    calc
      _ = ∑ q : BandPrime n W,
          (mu c).probability.expect ((mu c).I q.1) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [abs_of_nonneg ((mu c).probability.expect_nonneg _
          ((mu c).I_nonneg q.1))]
      _ ≤ ∑ q : BandPrime n W, G * (1 / (q.1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [BoundedValuationLaw.I] using
          hbase c q.1 (prime_of_mem_primeBand q.2).pos
      _ = AIrow := by
        dsimp only [AIrow, H]
        rw [← Finset.mul_sum, sum_bandPrime_inv_eq]
  have hJqBase (c : Cell) :
      (∑ q : BandPrime n W,
        |(mu c).probability.expect ((mu c).J q.1)|) ≤ AJrow := by
    calc
      _ ≤ ∑ q : BandPrime n W,
          2 * G * (1 / (q.1 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hqPrime := prime_of_mem_primeBand q.2
        rw [abs_of_nonneg ((mu c).probability.expect_nonneg _
          ((mu c).J_nonneg hqPrime))]
        exact expect_J_le_of_divisor_fallback
          (mu c) hqPrime hG (hbase c)
      _ = 2 * G * (∑ q : BandPrime n W,
          (1 / (q.1 : ℝ)) ^ 2) := by rw [Finset.mul_sum]
      _ = 2 * G * S₂ := by
        dsimp only [S₂]
        apply congrArg (fun z : ℝ ↦ 2 * G * z)
        calc
          (∑ q : BandPrime n W, (1 / (q.1 : ℝ)) ^ 2) =
              ∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            ring
          _ = bandReciprocalSquareSum n W := sum_bandPrime_inv_sq_eq n W
      _ ≤ AJrow := by
        dsimp only [AJrow, w₁]
        exact mul_le_mul_of_nonneg_left
          (bandReciprocalSquareSum_le n W hW.le) (by positivity)
  have hIpDiff (c : Cell) :
      |(nu c).probability.expect ((nu c).I p.1) -
        (mu c).probability.expect ((mu c).I p.1)| ≤ dIp := by
    simpa only [BoundedValuationLaw.I, dIp, e, p₁, mul_assoc] using
      hdiff c p.1 (prime_of_mem_primeBand p.2).pos
  have hJpDiff (c : Cell) :
      |(nu c).probability.expect ((nu c).J p.1) -
        (mu c).probability.expect ((mu c).J p.1)| ≤ dJp := by
    have hraw := abs_expect_J_sub_le_of_divisor_difference
        (nu c) (mu c) (prime_of_mem_primeBand p.2)
          (mul_nonneg he hG) (by
            intro D hD
            dsimp only [e]
            simpa only [mul_assoc] using hdiff c D hD)
    dsimp only [dJp, e, p₁]
    convert hraw using 1
    ring
  have hIqDiff (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).probability.expect ((nu c).I q.1) -
          (mu c).probability.expect ((mu c).I q.1)|) ≤ dIrow := by
    calc
      _ ≤ ∑ q : BandPrime n W,
          e * G * (1 / (q.1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [BoundedValuationLaw.I, e, mul_assoc] using
          hdiff c q.1 (prime_of_mem_primeBand q.2).pos
      _ = dIrow := by
        dsimp only [dIrow, H]
        rw [← Finset.mul_sum, sum_bandPrime_inv_eq]
  have hJqDiff (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).probability.expect ((nu c).J q.1) -
          (mu c).probability.expect ((mu c).J q.1)|) ≤ dJrow := by
    calc
      _ ≤ ∑ q : BandPrime n W,
          2 * e * G * (1 / (q.1 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [mul_assoc] using
          abs_expect_J_sub_le_of_divisor_difference
            (nu c) (mu c) (prime_of_mem_primeBand q.2)
              (mul_nonneg he hG) (by
                intro D hD
                dsimp only [e]
                simpa only [mul_assoc] using hdiff c D hD)
      _ = 2 * e * G * (∑ q : BandPrime n W,
          (1 / (q.1 : ℝ)) ^ 2) := by rw [Finset.mul_sum]
      _ = 2 * e * G * S₂ := by
        dsimp only [S₂]
        apply congrArg (fun z : ℝ ↦ 2 * e * G * z)
        calc
          (∑ q : BandPrime n W, (1 / (q.1 : ℝ)) ^ 2) =
              ∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            ring
          _ = bandReciprocalSquareSum n W := sum_bandPrime_inv_sq_eq n W
      _ ≤ dJrow := by
        dsimp only [dJrow, w₁]
        exact mul_le_mul_of_nonneg_left
          (bandReciprocalSquareSum_le n W hW.le) (by positivity)
  have hJI (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).covJI p.1 q.1 - (mu c).covJI p.1 q.1|) ≤ dJI := by
    simpa only [dJI, e, H, p₁] using
      sum_abs_covJI_sub_le_of_divisor_covariance_difference
        (nu c) (mu c) p he hG (hcov c)
  have hIJ (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).covIJ p.1 q.1 - (mu c).covIJ p.1 q.1|) ≤ dIJ := by
    simpa only [dIJ, e, S₂, p₁] using
      sum_abs_covIJ_sub_le_of_divisor_covariance_difference
        (nu c) (mu c) p he hG (hcov c)
  have hJJ (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).covJJ p.1 q.1 - (mu c).covJJ p.1 q.1|) ≤ dJJ := by
    simpa only [dJJ, e, S₂, p₁] using
      sum_abs_covJJ_sub_le_of_divisor_covariance_difference
        (nu c) (mu c) p he hG (hcov c)
  have hmix :=
    FiniteProbability.sum_abs_boundedValuationSigmaMixture_powerCorrection_sub_le
      weight mu nu p.1 (fun q : BandPrime n W ↦ q.1)
      hAIp hAJp hAIrow hAJrow hdIp0 hdJp0
      hIpBase hJpBase hIqBase hJqBase hIpDiff hJpDiff
      hIqDiff hJqDiff hJI hIJ hJJ
  simpa only [physicalPowerCorrectionMixtureBudget, e, H, S₂, w₁,
    p₁, AIp, AJp, AIrow, AJrow, dIp, dJp, dIrow, dJrow,
    dJI, dIJ, dJJ] using hmix







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_3 u_4
theorem solution :
∀ {Cell : Type u_3} [inst : Fintype.{u_3} Cell] {Omega : Cell → Type u_4}
  [inst_1 : (c : Cell) → Fintype.{u_4} (Omega c)] {M n W : Nat} (weight : Erdos390.Full.FiniteProbability.{u_3} Cell)
  (mu nu : (c : Cell) → Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_4} (Omega c) M)
  (p : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W) {epsilon G : Real},
  LE.le.{0} (0 : Real) epsilon →
    LE.le.{0} (0 : Real) G →
      LT.lt.{0} (1 : Nat) W →
        (∀ (c : Cell) (D : Nat),
            LT.lt.{0} (0 : Nat) D →
              LE.le.{0}
                (Erdos390.Full.FiniteProbability.expect.{u_4}
                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (mu c)) fun (x : Omega c) =>
                  Erdos390.Full.ArithmeticModel.divInd D
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (mu c) x))
                (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑D : Real)))) →
          (∀ (c : Cell) (D : Nat),
              LT.lt.{0} (0 : Nat) D →
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (Erdos390.Full.FiniteProbability.expect.{u_4}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (nu c))
                        fun (x : Omega c) =>
                        Erdos390.Full.ArithmeticModel.divInd D
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (nu c) x))
                      (Erdos390.Full.FiniteProbability.expect.{u_4}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (mu c))
                        fun (x : Omega c) =>
                        Erdos390.Full.ArithmeticModel.divInd D
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (mu c) x))))
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (8 : Real) epsilon) G)
                    (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑D : Real)))) →
            (∀ (c : Cell) (D E : Nat),
                LT.lt.{0} (0 : Nat) D →
                  LT.lt.{0} (0 : Nat) E →
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FiniteProbability.covariance.{u_4}
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (nu c))
                            (fun (x : Omega c) =>
                              Erdos390.Full.ArithmeticModel.divInd D
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (nu c) x))
                            fun (x : Omega c) =>
                            Erdos390.Full.ArithmeticModel.divInd E
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (nu c) x))
                          (Erdos390.Full.FiniteProbability.covariance.{u_4}
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (mu c))
                            (fun (x : Omega c) =>
                              Erdos390.Full.ArithmeticModel.divInd D
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (mu c) x))
                            fun (x : Omega c) =>
                            Erdos390.Full.ArithmeticModel.divInd E
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (mu c) x))))
                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (8 : Real) epsilon)
                        (HAdd.hAdd.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(Nat.lcm D E) : Real)))
                          (HMul.hMul.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} (3 : Real)
                              (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑D : Real))))
                            (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑E : Real))))))) →
              LE.le.{0}
                (∑ q : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W,
                  abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{max u_3 u_4}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_3, u_4} weight nu)
                          (↑p : Nat) (↑q : Nat))
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{max u_3 u_4}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_3, u_4} weight nu)
                          (↑p : Nat) (↑q : Nat)))
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{max u_3 u_4}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_3, u_4} weight mu)
                          (↑p : Nat) (↑q : Nat))
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{max u_3 u_4}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_3, u_4} weight mu)
                          (↑p : Nat) (↑q : Nat)))))
                (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget epsilon G n W (↑p : Nat)) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds
