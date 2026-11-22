-- Prove2me | solution 1 for Erdos390.Full.PaperGuardCensus.sum_abs_guardDeleted_powerCorrectionRow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:22:45.466067+00:00
-- url     : https://prove2.me/submissions/6fea755c-8249-4b3f-9cc4-4ea17a951476

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









end Erdos390.Full.ArithmeticModel

end

/- Source module: Erdos390.Full.GuardDeletionProbability -/
section


/-!
# Exact perturbation bounds for deleting a finite guard set

This module contains the finite-probability algebra used by the guarded-cell
corollary after the arithmetic guard census supplies a cardinality bound.
Deletion is defined on the original finite sample type (guarded points receive
mass zero) and is normalized exactly.  The expectation and covariance losses
are proved from the deleted mass; they are not stored in a certificate.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]



omit [DecidableEq Omega] in
theorem guardMass_nonneg (mu : FiniteProbability Omega) (G : Finset Omega) :
    0 ≤ mu.guardMass G :=
  Finset.sum_nonneg fun x _ => mu.mass_nonneg x



/- A guard census and a point-mass bound give the deleted-mass bound used in
the marked-cell application.  This is an inequality for the actual deleted
set, rather than a total-variation hypothesis stored in a certificate. -/


















/-- Exact expectation formula after guard deletion. -/
theorem deleteGuards_expect
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1) (F : Omega → ℝ) :
    (mu.deleteGuards G hsmall).expect F =
      (mu.expect F - mu.guardMoment G F) / (1 - mu.guardMass G) := by
  unfold expect guardMoment
  have hsplit := Finset.sum_sdiff (Finset.subset_univ G)
    (f := fun x => mu.mass x * F x)
  change (∑ x, (if x ∈ G then 0 else
      mu.mass x / (1 - mu.guardMass G)) * F x) = _
  calc
    (∑ x, (if x ∈ G then 0 else
        mu.mass x / (1 - mu.guardMass G)) * F x) =
        ∑ x ∈ (Finset.univ \ G),
          (mu.mass x * F x) / (1 - mu.guardMass G) := by
      rw [Finset.sdiff_eq_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxG : x ∈ G
      · simp [hxG]
      · simp [hxG]
        ring
    _ = (∑ x ∈ (Finset.univ \ G), mu.mass x * F x) /
        (1 - mu.guardMass G) := by rw [Finset.sum_div]
    _ = ((∑ x, mu.mass x * F x) -
          ∑ x ∈ G, mu.mass x * F x) /
        (1 - mu.guardMass G) := by
      congr 1
      linarith



omit [DecidableEq Omega] in
theorem guardPerturbation_nonneg
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1) :
    0 ≤ mu.guardPerturbation G := by
  unfold guardPerturbation
  exact div_nonneg (mul_nonneg (by norm_num) (mu.guardMass_nonneg G))
    (sub_pos.mpr hsmall).le

/- On the paper's small-deletion regime, the exact renormalization loss is
at most four times the deleted probability mass. -/


omit [DecidableEq Omega] in
/- Absolute expectation under a finite probability is bounded by any
pointwise absolute envelope. -/
theorem abs_expect_le_of_abs_le
    (mu : FiniteProbability Omega) (F : Omega → ℝ) {K : ℝ}
    (_hK : 0 ≤ K) (hF : ∀ x, |F x| ≤ K) :
    |mu.expect F| ≤ K := by
  unfold expect
  calc
    |∑ x, mu.mass x * F x| ≤
        ∑ x, |mu.mass x * F x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, mu.mass x * |F x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ ≤ ∑ x, mu.mass x * K := by
      exact Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hF x) (mu.mass_nonneg x)
    _ = K := by rw [← Finset.sum_mul, mu.mass_sum, one_mul]

omit [DecidableEq Omega] in
theorem abs_guardMoment_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (F : Omega → ℝ) {K : ℝ} (_hK : 0 ≤ K)
    (hF : ∀ x, |F x| ≤ K) :
    |mu.guardMoment G F| ≤ mu.guardMass G * K := by
  unfold guardMoment guardMass
  calc
    |∑ x ∈ G, mu.mass x * F x| ≤
        ∑ x ∈ G, |mu.mass x * F x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ G, mu.mass x * |F x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ ≤ ∑ x ∈ G, mu.mass x * K := by
      exact Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hF x) (mu.mass_nonneg x)
    _ = (∑ x ∈ G, mu.mass x) * K := by rw [Finset.sum_mul]

/-- Quantitative expectation perturbation after deleting guards. -/
theorem abs_deleteGuards_expect_sub_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1)
    (F : Omega → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ x, |F x| ≤ K) :
    |(mu.deleteGuards G hsmall).expect F - mu.expect F| ≤
      K * mu.guardPerturbation G := by
  let delta := mu.guardMass G
  let E := mu.expect F
  let R := mu.guardMoment G F
  have hdelta0 : 0 ≤ delta := mu.guardMass_nonneg G
  have hden : 0 < 1 - delta := sub_pos.mpr hsmall
  have hE : |E| ≤ K := mu.abs_expect_le_of_abs_le F hK hF
  have hR : |R| ≤ delta * K := by
    simpa only [delta, R] using mu.abs_guardMoment_le G F hK hF
  rw [mu.deleteGuards_expect G hsmall F]
  have hre : (E - R) / (1 - delta) - E =
      (delta * E - R) / (1 - delta) := by
    field_simp [ne_of_gt hden]
    ring
  change |(E - R) / (1 - delta) - E| ≤ _
  rw [hre, abs_div, abs_of_pos hden]
  calc
    |delta * E - R| / (1 - delta) ≤
        (delta * |E| + |R|) / (1 - delta) := by
      apply div_le_div_of_nonneg_right _ hden.le
      calc
        |delta * E - R| ≤ |delta * E| + |R| := abs_sub _ _
        _ = delta * |E| + |R| := by
          rw [abs_mul, abs_of_nonneg hdelta0]
    _ ≤ (delta * K + delta * K) / (1 - delta) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left hE hdelta0) hR
    _ = K * mu.guardPerturbation G := by
      unfold guardPerturbation
      dsimp only [delta]
      ring



end

end FiniteProbability
end Erdos390.Full

end

/- Source module: Erdos390.Full.GuardDeletionFamilyRows -/
section


/-!
# Family-summed guard-deletion bounds

A pointwise covariance perturbation followed by a sum over every medium prime
would lose the cardinality of the prime band.  The paper instead uses that, on
each integer, the *total* medium-prime valuation is `O(log n)`.  The lemmas in
this file formalize exactly that argument for an arbitrary finite family.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Omega I : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype I]

omit [DecidableEq Omega] in
/-- Summing absolute expectations costs the pointwise `l¹` envelope of the
whole family, not the cardinality of the index set. -/
theorem sum_abs_expect_le_familyEnvelope
    (mu : FiniteProbability Omega) (H : I → Omega → ℝ)
    {K : ℝ}
    (henv : ∀ x, ∑ i, |H i x| ≤ K) :
    ∑ i, |mu.expect (H i)| ≤ K := by
  calc
    ∑ i, |mu.expect (H i)| ≤
        ∑ i, ∑ x, mu.mass x * |H i x| := by
      apply Finset.sum_le_sum
      intro i hi
      unfold expect
      calc
        |∑ x, mu.mass x * H i x| ≤
            ∑ x, |mu.mass x * H i x| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x, mu.mass x * |H i x| := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ = ∑ x, mu.mass x * ∑ i, |H i x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ ≤ ∑ x, mu.mass x * K := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (henv x) (mu.mass_nonneg x)
    _ = K := by rw [← Finset.sum_mul, mu.mass_sum, one_mul]

omit [DecidableEq Omega] in
/-- The same family envelope controls the sum of all unnormalized guard
moments. -/
theorem sum_abs_guardMoment_le_familyEnvelope
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (H : I → Omega → ℝ) {K : ℝ}
    (henv : ∀ x, ∑ i, |H i x| ≤ K) :
    ∑ i, |mu.guardMoment G (H i)| ≤ mu.guardMass G * K := by
  calc
    ∑ i, |mu.guardMoment G (H i)| ≤
        ∑ i, ∑ x ∈ G, mu.mass x * |H i x| := by
      apply Finset.sum_le_sum
      intro i hi
      unfold guardMoment
      calc
        |∑ x ∈ G, mu.mass x * H i x| ≤
            ∑ x ∈ G, |mu.mass x * H i x| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x ∈ G, mu.mass x * |H i x| := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ = ∑ x ∈ G, mu.mass x * ∑ i, |H i x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ G, mu.mass x * K := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (henv x) (mu.mass_nonneg x)
    _ = mu.guardMass G * K := by
      unfold guardMass
      rw [Finset.sum_mul]

/-- Family-summed expectation perturbation.  The proof uses the exact
conditional-normalization formula and therefore has no hidden factor
`card I`. -/
theorem sum_abs_deleteGuards_expect_sub_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1)
    (H : I → Omega → ℝ) {K : ℝ}
    (henv : ∀ x, ∑ i, |H i x| ≤ K) :
    ∑ i,
        |(mu.deleteGuards G hsmall).expect (H i) - mu.expect (H i)| ≤
      K * mu.guardPerturbation G := by
  let delta := mu.guardMass G
  let nu := mu.deleteGuards G hsmall
  have hdelta0 : 0 ≤ delta := mu.guardMass_nonneg G
  have hden : 0 < 1 - delta := sub_pos.mpr hsmall
  have hE := mu.sum_abs_expect_le_familyEnvelope H henv
  have hR := mu.sum_abs_guardMoment_le_familyEnvelope G H henv
  have hpoint (i : I) :
      |nu.expect (H i) - mu.expect (H i)| ≤
        (delta * |mu.expect (H i)| + |mu.guardMoment G (H i)|) /
          (1 - delta) := by
    rw [show nu.expect (H i) =
        (mu.expect (H i) - mu.guardMoment G (H i)) / (1 - delta) by
      simpa only [nu, delta] using mu.deleteGuards_expect G hsmall (H i)]
    have hid :
        (mu.expect (H i) - mu.guardMoment G (H i)) / (1 - delta) -
            mu.expect (H i) =
          (delta * mu.expect (H i) - mu.guardMoment G (H i)) /
            (1 - delta) := by
      field_simp [hden.ne']
      ring
    rw [hid, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      |delta * mu.expect (H i) - mu.guardMoment G (H i)| ≤
          |delta * mu.expect (H i)| + |mu.guardMoment G (H i)| :=
        abs_sub _ _
      _ = delta * |mu.expect (H i)| + |mu.guardMoment G (H i)| := by
        rw [abs_mul, abs_of_nonneg hdelta0]
  calc
    ∑ i, |nu.expect (H i) - mu.expect (H i)| ≤
        ∑ i,
          (delta * |mu.expect (H i)| + |mu.guardMoment G (H i)|) /
            (1 - delta) := Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (delta * (∑ i, |mu.expect (H i)|) +
          ∑ i, |mu.guardMoment G (H i)|) / (1 - delta) := by
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (delta * K + delta * K) / (1 - delta) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact add_le_add (mul_le_mul_of_nonneg_left hE hdelta0) hR
    _ = K * mu.guardPerturbation G := by
      unfold guardPerturbation
      dsimp only [delta]
      ring

/-- Family-summed covariance perturbation.  This is the row estimate needed
for guard deletion: its right side sees the pointwise sum of the marked
statistics, never their number. -/
theorem sum_abs_deleteGuards_covariance_sub_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1)
    (F : Omega → ℝ) (H : I → Omega → ℝ)
    {KF KH : ℝ} (hKF : 0 ≤ KF)
    (hF : ∀ x, |F x| ≤ KF)
    (hH : ∀ x, ∑ i, |H i x| ≤ KH) :
    ∑ i,
        |(mu.deleteGuards G hsmall).covariance F (H i) -
          mu.covariance F (H i)| ≤
      3 * KF * KH * mu.guardPerturbation G := by
  let nu := mu.deleteGuards G hsmall
  let d := mu.guardPerturbation G
  let FH : I → Omega → ℝ := fun i x ↦ F x * H i x
  have hd0 : 0 ≤ d := mu.guardPerturbation_nonneg G hsmall
  have hFH : ∀ x, ∑ i, |FH i x| ≤ KF * KH := by
    intro x
    calc
      ∑ i, |FH i x| = |F x| * ∑ i, |H i x| := by
        simp only [FH, abs_mul, Finset.mul_sum]
      _ ≤ KF * KH := mul_le_mul (hF x) (hH x) (by positivity) hKF
  have hprod : ∑ i, |nu.expect (FH i) - mu.expect (FH i)| ≤
      (KF * KH) * d := by
    simpa only [nu, d] using
      mu.sum_abs_deleteGuards_expect_sub_le G hsmall FH
        hFH
  have hHdiff : ∑ i, |nu.expect (H i) - mu.expect (H i)| ≤
      KH * d := by
    simpa only [nu, d] using
      mu.sum_abs_deleteGuards_expect_sub_le G hsmall H hH
  have hnuH : ∑ i, |nu.expect (H i)| ≤ KH :=
    nu.sum_abs_expect_le_familyEnvelope H hH
  have hmuF : |mu.expect F| ≤ KF :=
    mu.abs_expect_le_of_abs_le F hKF hF
  have hFdiff : |nu.expect F - mu.expect F| ≤ KF * d := by
    simpa only [nu, d] using
      mu.abs_deleteGuards_expect_sub_le G hsmall F hKF hF
  have hpoint (i : I) :
      |nu.covariance F (H i) - mu.covariance F (H i)| ≤
        |nu.expect (FH i) - mu.expect (FH i)| +
          |nu.expect F - mu.expect F| * |nu.expect (H i)| +
          |mu.expect F| * |nu.expect (H i) - mu.expect (H i)| := by
    unfold covariance
    have hmean :
        nu.expect F * nu.expect (H i) - mu.expect F * mu.expect (H i) =
          (nu.expect F - mu.expect F) * nu.expect (H i) +
            mu.expect F * (nu.expect (H i) - mu.expect (H i)) := by ring
    rw [show
      (nu.expect (fun x ↦ F x * H i x) -
          nu.expect F * nu.expect (H i)) -
        (mu.expect (fun x ↦ F x * H i x) -
          mu.expect F * mu.expect (H i)) =
        (nu.expect (FH i) - mu.expect (FH i)) -
          (nu.expect F * nu.expect (H i) -
            mu.expect F * mu.expect (H i)) by
          simp only [FH]
          ring,
      hmean]
    let A := nu.expect (FH i) - mu.expect (FH i)
    let B₁ := (nu.expect F - mu.expect F) * nu.expect (H i)
    let B₂ := mu.expect F * (nu.expect (H i) - mu.expect (H i))
    have houter : |A - (B₁ + B₂)| ≤ |A| + |B₁ + B₂| :=
      abs_sub A (B₁ + B₂)
    have hinner : |B₁ + B₂| ≤ |B₁| + |B₂| := abs_add_le B₁ B₂
    have htotal : |A - (B₁ + B₂)| ≤ |A| + |B₁| + |B₂| := by
      exact houter.trans (by linarith)
    dsimp only [A, B₁, B₂] at htotal
    simpa only [abs_mul] using htotal
  calc
    ∑ i, |nu.covariance F (H i) - mu.covariance F (H i)| ≤
        ∑ i, (|nu.expect (FH i) - mu.expect (FH i)| +
          |nu.expect F - mu.expect F| * |nu.expect (H i)| +
          |mu.expect F| * |nu.expect (H i) - mu.expect (H i)|) :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (∑ i, |nu.expect (FH i) - mu.expect (FH i)|) +
          |nu.expect F - mu.expect F| * (∑ i, |nu.expect (H i)|) +
          |mu.expect F| *
            (∑ i, |nu.expect (H i) - mu.expect (H i)|) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum]
    _ ≤ (KF * KH) * d + (KF * d) * KH + KF * (KH * d) := by
      exact add_le_add
        (add_le_add hprod
          (mul_le_mul hFdiff hnuH (by positivity) (mul_nonneg hKF hd0)))
        (mul_le_mul hmuF hHdiff (by positivity) hKF)
    _ = 3 * KF * KH * mu.guardPerturbation G := by
      dsimp only [d]
      ring

end

end Erdos390.Full.FiniteProbability

end

/- Source module: Erdos390.Full.PaperGuardDeletionRows -/
section


/-!
# Prime-row perturbations from the concrete guard deletion

The central estimate is family-summed.  Thus the row cost is controlled by
the total valuation of one integer, `O(log n / log W)`, rather than by the
number of primes in the moving band.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability GuardedUniformCell
open ValuationTiltCell ArithmeticBandGeometry
open PaperScaleMarkedCell

noncomputable section

variable {Alpha I : Type*} [DecidableEq Alpha] [Fintype I]





/-- Uniform valuation envelope on a literal raw physical cell. -/
theorem rawCell_totalBandValuation_le
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W : ℕ} (hW : 1 < W) (c : PaperBridgeFit.Cell Head)
    (m : rawCell P Iphys n c) :
    (∑ q : BandPrime n W, valuation q.1 (m : ℕ)) ≤
      Real.log (physicalBound (Iphys.upper c.2) n : ℝ) /
        Real.log (W : ℝ) := by
  have hm : 0 < (m : ℕ) := by
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hmM : (m : ℕ) ≤ physicalBound (Iphys.upper c.2) n := by
    exact (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have hpW : ∀ q ∈ primeBand n W, W ≤ q := by
    intro q hq
    exact (cutoff_lt_of_mem_primeBand hq).le
  have hraw := sum_valuation_le_log_ratio (primeBand n W) hm hmM hW hpW
  calc
    (∑ q : BandPrime n W, valuation q.1 (m : ℕ)) =
        ∑ q ∈ (primeBand n W).attach, valuation q.1 (m : ℕ) := by
      change (∑ q : primeBand n W, valuation q.1 (m : ℕ)) = _
      rfl
    _ = ∑ q ∈ primeBand n W, valuation q (m : ℕ) :=
      Finset.sum_attach (primeBand n W) (fun q ↦ valuation q (m : ℕ))
    _ ≤ _ := hraw



/-- A single medium-prime valuation is bounded by the total valuation
envelope. -/
theorem rawCell_valuation_le_total
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n W : ℕ} (p : BandPrime n W) (c : PaperBridgeFit.Cell Head)
    (m : rawCell P Iphys n c) :
    valuation p.1 (m : ℕ) ≤
      ∑ q : BandPrime n W, valuation q.1 (m : ℕ) := by
  exact Finset.single_le_sum (fun q hq ↦ valuation_nonneg q.1 (m : ℕ))
    (Finset.mem_univ p)









end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.FiniteProbabilityMixturePerturbation -/
section


/-!
# Family-summed perturbations of finite tagged mixtures

The covariance of a tagged mixture contains a between-component term.  Thus
componentwise covariance estimates alone cannot be averaged.  This file
works one level lower: component first moments and mixed moments are compared,
then the exact sigma-mixture expectation formula is used before covariance is
formed.  The resulting theorem keeps an entire finite covariance row under a
single family envelope and includes the between-component contribution.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Cell I : Type*} [Fintype Cell] [Fintype I]
  {Omega Theta : Cell → Type*}
  [∀ c, Fintype (Omega c)] [∀ c, Fintype (Theta c)]











/-- Concrete specialization to deleting guards independently in every
component while keeping the same tagged mixture weights.  The bound is
family-summed before mixing, so neither the number of components nor the
number of row indices appears. -/
theorem sum_abs_sigmaMixture_deleteGuards_covariance_sub_le
    [∀ c, DecidableEq (Omega c)]
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (guards : ∀ c, Finset (Omega c))
    (hsmall : ∀ c, (mu c).guardMass (guards c) < 1)
    (F : ∀ c, Omega c → ℝ) (H : ∀ c, I → Omega c → ℝ)
    {KF KH d : ℝ}
    (hKF : 0 ≤ KF) (hKH : 0 ≤ KH) (hd : 0 ≤ d)
    (hF : ∀ c x, |F c x| ≤ KF)
    (hH : ∀ c x, ∑ i, |H c i x| ≤ KH)
    (hperturb : ∀ c, (mu c).guardPerturbation (guards c) ≤ d) :
    ∑ i, |(sigmaMixture weight
          (fun c ↦ (mu c).deleteGuards (guards c) (hsmall c))).covariance
          (fun x ↦ F x.1 x.2) (fun x ↦ H x.1 i x.2) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ F x.1 x.2) (fun x ↦ H x.1 i x.2)| ≤
      3 * KF * KH * d +
        2 * ((KF + KF * d) * (KH * d) + KH * (KF * d)) := by
  let nu : ∀ c, FiniteProbability (Omega c) :=
    fun c ↦ (mu c).deleteGuards (guards c) (hsmall c)
  have hFbase (c : Cell) : |(mu c).expect (F c)| ≤ KF :=
    (mu c).abs_expect_le_of_abs_le (F c) hKF (hF c)
  have hHbase (c : Cell) : ∑ i, |(mu c).expect (H c i)| ≤ KH :=
    (mu c).sum_abs_expect_le_familyEnvelope (H c) (hH c)
  have hFdiff (c : Cell) :
      |(nu c).expect (F c) - (mu c).expect (F c)| ≤ KF * d := by
    have hraw := (mu c).abs_deleteGuards_expect_sub_le
      (guards c) (hsmall c) (F c) hKF (hF c)
    exact hraw.trans (mul_le_mul_of_nonneg_left (hperturb c) hKF)
  have hHdiff (c : Cell) : ∑ i,
      |(nu c).expect (H c i) - (mu c).expect (H c i)| ≤ KH * d := by
    have hraw := (mu c).sum_abs_deleteGuards_expect_sub_le
      (guards c) (hsmall c) (H c) (hH c)
    exact hraw.trans (mul_le_mul_of_nonneg_left (hperturb c) hKH)
  have hCovdiff (c : Cell) : ∑ i,
      |(nu c).covariance (F c) (H c i) -
        (mu c).covariance (F c) (H c i)| ≤ 3 * KF * KH * d := by
    have hraw := (mu c).sum_abs_deleteGuards_covariance_sub_le
      (guards c) (hsmall c) (F c) (H c) hKF (hF c) (hH c)
    have hcoef : 0 ≤ 3 * KF * KH := by positivity
    exact hraw.trans (mul_le_mul_of_nonneg_left (hperturb c) hcoef)
  have hmain := sum_abs_sigmaMixture_covariance_sub_le_of_component_covariance
    weight mu nu F F H H hKF hKH (mul_nonneg hKF hd)
      hFbase hHbase hFdiff hHdiff hCovdiff
  simpa only [nu] using hmain

end

end Erdos390.Full.FiniteProbability

end

/- Source module: Erdos390.Full.PaperGuardPowerCorrectionMixture -/
section


/-!
# Guard deletion for the global prime-power correction row

The useful object in Lemma 7.5 is not the full valuation covariance by
itself, but its difference from the squarefree covariance.  This file applies
the family-summed tagged-mixture perturbation theorem separately to the `VV`
and `II` rows and then subtracts them.  The estimate is global: arbitrary
common component weights and every between-cell covariance term are included.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel ArithmeticBandGeometry FiniteProbability PaperBridgeFit

noncomputable section







variable {Head : Type*} [Fintype Head]

/-- Deleting guards componentwise perturbs the global `VV-II` row by the
displayed family error.  The hypothesis `hperturb` is a bound for the exact
conditional-normalization factor, not a total-variation proxy. -/
theorem sum_abs_guardDeleted_powerCorrectionRow_sub_le
    (P : Head → HeadPattern.Pattern) (Iphys : PhysicalIntervals)
    {n W : ℕ} (hW : 1 < W)
    (guardsNat : Finset ℕ)
    (hS : ∀ c : Cell Head, (rawCell P Iphys n c).Nonempty)
    (score : ∀ c : Cell Head, rawCell P Iphys n c → ℝ)
    (weight : FiniteProbability (Cell Head))
    (p : BandPrime n W)
    {K d : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hEnvelope : ∀ c : Cell Head,
      valuationEnvelope Iphys n W c ≤ K)
    (hsmall : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P Iphys n c) (hS c)).exponentialTilt
          (score c)).guardMass
        (GuardedUniformCell.guardSubtype
          (rawCell P Iphys n c) guardsNat) < 1))
    (hperturb : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P Iphys n c) (hS c)).exponentialTilt
          (score c)).guardPerturbation
        (GuardedUniformCell.guardSubtype
          (rawCell P Iphys n c) guardsNat) ≤ d)) :
    let S := fun c : Cell Head ↦ rawCell P Iphys n c
    let mu : ∀ c, FiniteProbability (S c) := fun c ↦
      (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
    let Gsub : ∀ c, Finset (S c) := fun c ↦
      GuardedUniformCell.guardSubtype (S c) guardsNat
    let nu : ∀ c, FiniteProbability (S c) := fun c ↦
      (mu c).deleteGuards (Gsub c) (hsmall c)
    let value : (Sigma fun c : Cell Head ↦ S c) → ℕ :=
      fun x ↦ (x.2 : ℕ)
    ∑ q : BandPrime n W,
      |powerCorrectionCovariance (sigmaMixture weight nu) value p.1 q.1 -
        powerCorrectionCovariance (sigmaMixture weight mu) value p.1 q.1| ≤
      guardPowerCorrectionRowError K d := by
  dsimp only
  let S := fun c : Cell Head ↦ rawCell P Iphys n c
  let mu : ∀ c, FiniteProbability (S c) := fun c ↦
    (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
  let Gsub : ∀ c, Finset (S c) := fun c ↦
    GuardedUniformCell.guardSubtype (S c) guardsNat
  let nu : ∀ c, FiniteProbability (S c) := fun c ↦
    (mu c).deleteGuards (Gsub c) (hsmall c)
  let Fv : ∀ c, S c → ℝ := fun _ m ↦ valuation p.1 (m : ℕ)
  let Hv : ∀ c, BandPrime n W → S c → ℝ :=
    fun _ q m ↦ valuation q.1 (m : ℕ)
  let Fi : ∀ c, S c → ℝ := fun _ m ↦ divInd p.1 (m : ℕ)
  let Hi : ∀ c, BandPrime n W → S c → ℝ :=
    fun _ q m ↦ divInd q.1 (m : ℕ)
  have htotal (c : Cell Head) (m : S c) :
      ∑ q : BandPrime n W, valuation q.1 (m : ℕ) ≤ K :=
    (rawCell_totalBandValuation_le P Iphys hW c m).trans (hEnvelope c)
  have hFv (c : Cell Head) (m : S c) : |Fv c m| ≤ K := by
    rw [abs_of_nonneg (valuation_nonneg p.1 (m : ℕ))]
    exact (rawCell_valuation_le_total P Iphys p c m).trans (htotal c m)
  have hHv (c : Cell Head) (m : S c) :
      ∑ q : BandPrime n W, |Hv c q m| ≤ K := by
    simpa only [Hv, abs_of_nonneg (valuation_nonneg _ _)] using htotal c m
  have hFi (c : Cell Head) (m : S c) : |Fi c m| ≤ (1 : ℝ) := by
    dsimp only [Fi]
    rw [abs_of_nonneg (divInd_nonneg p.1 (m : ℕ))]
    exact divInd_le_one p.1 (m : ℕ)
  have hHi (c : Cell Head) (m : S c) :
      ∑ q : BandPrime n W, |Hi c q m| ≤ K := by
    calc
      ∑ q : BandPrime n W, |Hi c q m| ≤
          ∑ q : BandPrime n W, valuation q.1 (m : ℕ) := by
        apply Finset.sum_le_sum
        intro q hq
        dsimp only [Hi]
        rw [abs_of_nonneg (divInd_nonneg q.1 (m : ℕ))]
        have hmpos : 0 < (m : ℕ) :=
          StructuredCells.pos_of_mem_smoothInterval
            (StructuredCells.mem_structuredCell.mp m.2).1
        have hhigher := higherValuation_nonneg
          (prime_of_mem_primeBand q.2) hmpos
        unfold higherValuation at hhigher
        linarith
      _ ≤ K := htotal c m
  have hsmall' (c : Cell Head) : (mu c).guardMass (Gsub c) < 1 := by
    simpa only [mu, Gsub, S] using hsmall c
  have hperturb' (c : Cell Head) :
      (mu c).guardPerturbation (Gsub c) ≤ d := by
    simpa only [mu, Gsub, S] using hperturb c
  have hfull := sum_abs_sigmaMixture_deleteGuards_covariance_sub_le
    weight mu Gsub hsmall' Fv Hv hK hK hd hFv hHv hperturb'
  have hsquare := sum_abs_sigmaMixture_deleteGuards_covariance_sub_le
    weight mu Gsub hsmall' Fi Hi (by norm_num) hK hd hFi hHi hperturb'
  have hpoint (q : BandPrime n W) :
      |powerCorrectionCovariance (sigmaMixture weight nu)
          (fun x : (Sigma fun c : Cell Head ↦ S c) ↦ (x.2 : ℕ)) p.1 q.1 -
        powerCorrectionCovariance (sigmaMixture weight mu)
          (fun x : (Sigma fun c : Cell Head ↦ S c) ↦ (x.2 : ℕ)) p.1 q.1| ≤
        |(sigmaMixture weight nu).covariance
            (fun x ↦ valuation p.1 (x.2 : ℕ))
            (fun x ↦ valuation q.1 (x.2 : ℕ)) -
          (sigmaMixture weight mu).covariance
            (fun x ↦ valuation p.1 (x.2 : ℕ))
            (fun x ↦ valuation q.1 (x.2 : ℕ))| +
        |(sigmaMixture weight nu).covariance
            (fun x ↦ divInd p.1 (x.2 : ℕ))
            (fun x ↦ divInd q.1 (x.2 : ℕ)) -
          (sigmaMixture weight mu).covariance
            (fun x ↦ divInd p.1 (x.2 : ℕ))
            (fun x ↦ divInd q.1 (x.2 : ℕ))| := by
    unfold powerCorrectionCovariance
    rw [show
      ((sigmaMixture weight nu).covariance
          (fun x ↦ valuation p.1 (x.2 : ℕ))
          (fun x ↦ valuation q.1 (x.2 : ℕ)) -
        (sigmaMixture weight nu).covariance
          (fun x ↦ divInd p.1 (x.2 : ℕ))
          (fun x ↦ divInd q.1 (x.2 : ℕ))) -
      ((sigmaMixture weight mu).covariance
          (fun x ↦ valuation p.1 (x.2 : ℕ))
          (fun x ↦ valuation q.1 (x.2 : ℕ)) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ divInd p.1 (x.2 : ℕ))
          (fun x ↦ divInd q.1 (x.2 : ℕ))) =
      ((sigmaMixture weight nu).covariance
          (fun x ↦ valuation p.1 (x.2 : ℕ))
          (fun x ↦ valuation q.1 (x.2 : ℕ)) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ valuation p.1 (x.2 : ℕ))
          (fun x ↦ valuation q.1 (x.2 : ℕ))) -
      ((sigmaMixture weight nu).covariance
          (fun x ↦ divInd p.1 (x.2 : ℕ))
          (fun x ↦ divInd q.1 (x.2 : ℕ)) -
        (sigmaMixture weight mu).covariance
          (fun x ↦ divInd p.1 (x.2 : ℕ))
          (fun x ↦ divInd q.1 (x.2 : ℕ))) by ring]
    exact abs_sub _ _
  calc
    ∑ q : BandPrime n W,
      |powerCorrectionCovariance (sigmaMixture weight nu)
          (fun x : (Sigma fun c : Cell Head ↦ S c) ↦ (x.2 : ℕ)) p.1 q.1 -
        powerCorrectionCovariance (sigmaMixture weight mu)
          (fun x : (Sigma fun c : Cell Head ↦ S c) ↦ (x.2 : ℕ)) p.1 q.1| ≤
      ∑ q : BandPrime n W,
        (|(sigmaMixture weight nu).covariance
              (fun x ↦ valuation p.1 (x.2 : ℕ))
              (fun x ↦ valuation q.1 (x.2 : ℕ)) -
            (sigmaMixture weight mu).covariance
              (fun x ↦ valuation p.1 (x.2 : ℕ))
              (fun x ↦ valuation q.1 (x.2 : ℕ))| +
          |(sigmaMixture weight nu).covariance
              (fun x ↦ divInd p.1 (x.2 : ℕ))
              (fun x ↦ divInd q.1 (x.2 : ℕ)) -
            (sigmaMixture weight mu).covariance
              (fun x ↦ divInd p.1 (x.2 : ℕ))
              (fun x ↦ divInd q.1 (x.2 : ℕ))|) :=
      Finset.sum_le_sum fun q hq ↦ hpoint q
    _ = (∑ q : BandPrime n W,
          |(sigmaMixture weight nu).covariance
              (fun x ↦ valuation p.1 (x.2 : ℕ))
              (fun x ↦ valuation q.1 (x.2 : ℕ)) -
            (sigmaMixture weight mu).covariance
              (fun x ↦ valuation p.1 (x.2 : ℕ))
              (fun x ↦ valuation q.1 (x.2 : ℕ))|) +
        ∑ q : BandPrime n W,
          |(sigmaMixture weight nu).covariance
              (fun x ↦ divInd p.1 (x.2 : ℕ))
              (fun x ↦ divInd q.1 (x.2 : ℕ)) -
            (sigmaMixture weight mu).covariance
              (fun x ↦ divInd p.1 (x.2 : ℕ))
              (fun x ↦ divInd q.1 (x.2 : ℕ))| := by
      rw [Finset.sum_add_distrib]
    _ ≤ (3 * K * K * d +
          2 * ((K + K * d) * (K * d) + K * (K * d))) +
        (3 * 1 * K * d +
          2 * ((1 + 1 * d) * (K * d) + K * (1 * d))) :=
      add_le_add (by simpa only [nu, Fv, Hv] using hfull)
        (by simpa only [nu, Fi, Hi] using hsquare)
    _ = guardPowerCorrectionRowError K d := by
      unfold guardPowerCorrectionRowError
      ring

end

end Erdos390.Full.PaperGuardCensus

end

universe u_1
theorem solution :
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern)
  (Iphys : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) {n W : Nat},
  LT.lt.{0} (1 : Nat) W →
    ∀ (guardsNat : Finset.{0} Nat)
      (hS :
        ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
          Finset.Nonempty.{0} (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c))
      (score :
        (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) →
          ↥(Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) → Real)
      (weight : Erdos390.Full.FiniteProbability.{u_1} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head))
      (p : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W) {K d : Real},
      LE.le.{0} (0 : Real) K →
        LE.le.{0} (0 : Real) d →
          (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
              LE.le.{0} (Erdos390.Full.PaperGuardCensus.valuationEnvelope.{u_1} Iphys n W c) K) →
            ∀
              (hsmall :
                ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  LT.lt.{0}
                    (Erdos390.Full.FiniteProbability.guardMass.{0}
                      (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                        (Erdos390.Full.FiniteProbability.uniformOnFinset.{0}
                          (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) (hS c))
                        (score c))
                      (Erdos390.Full.GuardedUniformCell.guardSubtype.{0}
                        (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) guardsNat))
                    (1 : Real)),
              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  LE.le.{0}
                    (Erdos390.Full.FiniteProbability.guardPerturbation.{0}
                      (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                        (Erdos390.Full.FiniteProbability.uniformOnFinset.{0}
                          (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) (hS c))
                        (score c))
                      (Erdos390.Full.GuardedUniformCell.guardSubtype.{0}
                        (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c) guardsNat))
                    d) →
                let S := fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                  Erdos390.Full.PaperGuardCensus.rawCell.{u_1} P Iphys n c;
                let mu := fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                  Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                    (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} (S c) (hS c)) (score c);
                let Gsub := fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                  Erdos390.Full.GuardedUniformCell.guardSubtype.{0} (S c) guardsNat;
                have nu := fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                  Erdos390.Full.FiniteProbability.deleteGuards.{0} (mu c) (Gsub c) (hsmall c);
                have value := fun (x : (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) × ↥(S c)) =>
                  ↑(Sigma.snd.{u_1, 0} x);
                LE.le.{0}
                  (∑ q : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W,
                    abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.PaperGuardCensus.powerCorrectionCovariance.{u_1}
                          (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, 0} weight nu) value ↑p ↑q)
                        (Erdos390.Full.PaperGuardCensus.powerCorrectionCovariance.{u_1}
                          (Erdos390.Full.FiniteProbability.sigmaMixture.{u_1, 0} weight mu) value ↑p ↑q)))
                  (Erdos390.Full.PaperGuardCensus.guardPowerCorrectionRowError K d) := by
  exact @Erdos390.Full.PaperGuardCensus.sum_abs_guardDeleted_powerCorrectionRow_sub_le
