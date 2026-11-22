-- Prove2me | solution 1 for Erdos390.Full.GuardDeletionSquarefreeProfiles.exists_deleteGuards_squarefree_profiles
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:04:12.678923+00:00
-- url     : https://prove2.me/submissions/5fde34ce-be0f-4f68-92ff-bcb1ff5937d4

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

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





















































end Erdos390.Full.ArithmeticModel

end

/- Source module: Erdos390.Full.OmittedTiltFallback -/
section


/-!
# Arbitrary-modulus fallback under an omitted valuation tilt

The four-mark theorem gives the sharp Dickman main term.  Terms outside that
chamber only require an upper bound.  This file proves the required fallback
directly: a bounded exponential tilt changes every nonnegative event by at
most its pointwise density-ratio bound, and elementary multiple counting on
an actual positive cell gives the reciprocal divisor scale for every modulus.
-/

namespace Erdos390.Full

open ArithmeticModel DivisibilityMomentBounds

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- The partition function of a score bounded in absolute value by `K` is at
least `exp (-K)`. -/
theorem exp_neg_le_expPartition (mu : FiniteProbability Omega)
    (score : Omega → ℝ) (K : ℝ) (hscore : ∀ omega, |score omega| ≤ K) :
    Real.exp (-K) ≤ mu.expPartition score := by
  unfold expPartition expect
  calc
    Real.exp (-K) = ∑ omega, mu.mass omega * Real.exp (-K) := by
      rw [← Finset.sum_mul, mu.mass_sum, one_mul]
    _ ≤ ∑ omega, mu.mass omega * Real.exp (score omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
      exact Real.exp_le_exp.mpr ((neg_le_neg (hscore omega)).trans
        (neg_abs_le (score omega)))

/-- Pointwise bounded tilting changes any nonnegative expectation by at most
the exact density-ratio factor `exp (2K)`. -/
theorem exponentialTilt_expect_le_exp_two_mul
    (mu : FiniteProbability Omega) (A score : Omega → ℝ) (K : ℝ)
    (hA : ∀ omega, 0 ≤ A omega)
    (hscore : ∀ omega, |score omega| ≤ K) :
    (mu.exponentialTilt score).expect A ≤
      Real.exp (2 * K) * mu.expect A := by
  have hZpos : 0 < mu.expPartition score := mu.expPartition_pos score
  have hZlower : Real.exp (-K) ≤ mu.expPartition score :=
    mu.exp_neg_le_expPartition score K hscore
  have hEA0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA
  have hnum0 : 0 ≤ mu.expect (fun omega ↦ A omega * Real.exp (score omega)) :=
    mu.expect_nonneg _ fun omega ↦ mul_nonneg (hA omega) (Real.exp_pos _).le
  have hnum : mu.expect (fun omega ↦ A omega * Real.exp (score omega)) ≤
      Real.exp K * mu.expect A := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega homega
    calc
      mu.mass omega * (A omega * Real.exp (score omega)) ≤
          mu.mass omega * (A omega * Real.exp K) := by
        apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
        apply mul_le_mul_of_nonneg_left _ (hA omega)
        exact Real.exp_le_exp.mpr ((le_abs_self (score omega)).trans
          (hscore omega))
      _ = Real.exp K * (mu.mass omega * A omega) := by ring
  have hinv : (mu.expPartition score)⁻¹ ≤ Real.exp K := by
    apply (inv_le_iff_one_le_mul₀ hZpos).2
    calc
      1 = Real.exp K * Real.exp (-K) := by
        rw [← Real.exp_add]
        ring_nf
        simp
      _ ≤ Real.exp K * mu.expPartition score :=
        mul_le_mul_of_nonneg_left hZlower (Real.exp_pos K).le
  rw [mu.exponentialTilt_expect_eq A score, div_eq_mul_inv]
  calc
    mu.expect (fun omega ↦ A omega * Real.exp (score omega)) *
        (mu.expPartition score)⁻¹ ≤
      (Real.exp K * mu.expect A) * (mu.expPartition score)⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hZpos.le)
    _ ≤ (Real.exp K * mu.expect A) * Real.exp K :=
      mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (Real.exp_pos K).le hEA0)
    _ = Real.exp (2 * K) * mu.expect A := by
      rw [show Real.exp (2 * K) = Real.exp K * Real.exp K by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring

end FiniteProbability

namespace OmittedTiltFallback

open FiniteProbability ValuationScoreDomination ValuationTiltCell





end OmittedTiltFallback

end

end Erdos390.Full

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


/-- A bounded exponential tilt enlarges every individual atom by at most
the exact density-ratio factor `exp (2K)`. -/
theorem exponentialTilt_mass_le_exp_two_mul
    (mu : FiniteProbability Omega) (score : Omega → ℝ) (K : ℝ)
    (hscore : ∀ x, |score x| ≤ K) (x : Omega) :
    (mu.exponentialTilt score).mass x ≤ Real.exp (2 * K) * mu.mass x := by
  have h := mu.exponentialTilt_expect_le_exp_two_mul
    (fun y : Omega => if y = x then 1 else 0) score K
    (fun y => by by_cases hy : y = x <;> simp [hy]) hscore
  simpa [expect] using h

/-- The same density-ratio estimate summed over the actual guard set. -/
theorem exponentialTilt_guardMass_le_exp_two_mul
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (score : Omega → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K) :
    (mu.exponentialTilt score).guardMass G ≤
      Real.exp (2 * K) * mu.guardMass G := by
  unfold guardMass
  calc
    (∑ x ∈ G, (mu.exponentialTilt score).mass x) ≤
        ∑ x ∈ G, Real.exp (2 * K) * mu.mass x :=
      Finset.sum_le_sum fun x hx =>
        mu.exponentialTilt_mass_le_exp_two_mul score K hscore x
    _ = Real.exp (2 * K) * ∑ x ∈ G, mu.mass x := by
      rw [Finset.mul_sum]













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





/- On the paper's small-deletion regime, the exact renormalization loss is
at most four times the deleted probability mass. -/
omit [DecidableEq Omega] in
theorem guardPerturbation_le_four_mul_guardMass
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hhalf : mu.guardMass G ≤ (1 : ℝ) / 2) :
    mu.guardPerturbation G ≤ 4 * mu.guardMass G := by
  let delta := mu.guardMass G
  have hdelta0 : 0 ≤ delta := mu.guardMass_nonneg G
  have hden : 0 < 1 - delta := by
    dsimp only [delta] at hhalf ⊢
    linarith
  unfold guardPerturbation
  dsimp only [delta] at hdelta0 hden ⊢
  rw [div_le_iff₀ hden]
  nlinarith

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

/- Source module: Erdos390.Full.GuardedUniformCell -/
section


/-!
# Guard deletion on an actual uniform arithmetic cell

The paper deletes an ambient finite guard set from each structured cell.
This module constructs the literal guard subset of the cell, proves that its
cardinality is no larger than the ambient guard census, and combines that fact
with the bounded-tilt density ratio.  No total-variation or covariance error is
assumed.
-/

namespace Erdos390.Full

open FiniteProbability

noncomputable section

namespace GuardedUniformCell

variable {Alpha : Type*} [DecidableEq Alpha]





/-- The subtype guard census injects into the ambient guard census. -/
theorem card_guardSubtype_le (S G : Finset Alpha) :
    (guardSubtype S G).card ≤ G.card := by
  apply Finset.card_le_card_of_injOn (fun x : S => (x : Alpha))
  · intro x hx
    exact mem_guardSubtype.mp hx
  · intro x hx y hy hxy
    exact Subtype.ext hxy

/-- Exact deleted mass before tilting the uniform cell. -/
theorem uniform_guardMass_eq
    (S G : Finset Alpha) (hS : S.Nonempty) :
    (uniformOnFinset S hS).guardMass (guardSubtype S G) =
      ((guardSubtype S G).card : ℝ) / (S.card : ℝ) := by
  unfold guardMass
  simp only [uniformOnFinset_mass, Finset.sum_const, nsmul_eq_mul]
  ring

/-- A bounded tilt assigns the actual guard subset at most its ambient
cardinality divided by the actual cell cardinality, times `exp (2K)`. -/
theorem tilted_uniform_guardMass_le
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : S → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K) :
    ((uniformOnFinset S hS).exponentialTilt score).guardMass
        (guardSubtype S G) ≤
      Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) := by
  have hScard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hguardCard : ((guardSubtype S G).card : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast card_guardSubtype_le S G
  calc
    ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) ≤
        Real.exp (2 * K) *
          (uniformOnFinset S hS).guardMass (guardSubtype S G) :=
      (uniformOnFinset S hS).exponentialTilt_guardMass_le_exp_two_mul
        (guardSubtype S G) score K hscore
    _ = Real.exp (2 * K) *
          (((guardSubtype S G).card : ℝ) / (S.card : ℝ)) := by
      rw [uniform_guardMass_eq]
    _ ≤ Real.exp (2 * K) * ((G.card : ℝ) / (S.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hguardCard hScard.le)
        (Real.exp_pos _).le
    _ = Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) := by ring



end GuardedUniformCell

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.GuardDeletionSquarefreeProfiles -/
section


/-!
# Reciprocal signed profiles after guard deletion

For the signed squarefree comparison only divisors `p` and `pq` occur.
Although deleting guards first gives an additive probability error, the
paper census is much smaller than `1/y²`; multiplying by the explicit
`y²` factor therefore restores the required reciprocal scale.  This file
records the exact finite step, including renormalization.
-/

namespace Erdos390.Full.GuardDeletionSquarefreeProfiles

open ArithmeticModel Scale FiniteProbability GuardedUniformCell
open OmittedTiltPairChamber PaperPrimePowerChamberError
open PaperScaleMarkedCell

noncomputable section





/-- A common signed squarefree profile survives literal conditional guard
deletion.  The proof constructs the conditional law and includes the two
mean-renormalization losses through `abs_deleteGuards_expect_sub_le`; no
total-variation assertion is assumed. -/
theorem exists_deleteGuards_squarefree_profiles
    (S G : Finset ℕ) (hS : S.Nonempty)
    (score : S → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K)
    {n W : ℕ} {E : ℝ}
    (hsmallCensus :
      Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ) ≤ (1 : ℝ) / 2)
    (hpair : ∀ p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |((uniformOnFinset S hS).exponentialTilt score).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          E * pairWeight p q 1 1)
    (hsingle : ∀ p, p ∈ primeBand n W →
      |((uniformOnFinset S hS).exponentialTilt score).expect
          (fun m ↦ divInd p (m : ℕ)) -
        paperDivisibilityMain n p| ≤ E * singleWeight p 1) :
    ∃ hsmall :
        ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) < 1,
      let deleted :=
        ((uniformOnFinset S hS).exponentialTilt score).deleteGuards
          (guardSubtype S G) hsmall
      (∀ p, p ∈ primeBand n W →
        ∀ q, q ∈ (primeBand n W).erase p →
        |deleted.expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
          paperDivisibilityMain n (pairPower p q 1 1)| ≤
            (E + guardSquarefreeError S G K n) * pairWeight p q 1 1) ∧
      (∀ p, p ∈ primeBand n W →
        |deleted.expect (fun m ↦ divInd p (m : ℕ)) -
          paperDivisibilityMain n p| ≤
            (E + guardSquarefreeError S G K n) * singleWeight p 1) := by
  let mu := (uniformOnFinset S hS).exponentialTilt score
  let guards := guardSubtype S G
  let delta := Real.exp (2 * K) * (G.card : ℝ) / (S.card : ℝ)
  have hmass : mu.guardMass guards ≤ delta := by
    simpa only [mu, guards, delta] using
      tilted_uniform_guardMass_le S G hS score K hscore
  have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 :=
    hmass.trans hsmallCensus
  have hsmall : mu.guardMass guards < 1 := by linarith
  refine ⟨hsmall, ?_, ?_⟩
  · intro p hp q hq
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hq).2
    have hpPrime := prime_of_mem_primeBand hp
    have hqPrime := prime_of_mem_primeBand hqBand
    have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hp
    have hqY : q ≤ yNat n := le_yNat_of_mem_primeBand hqBand
    have hpPosR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hqPosR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqPrime.pos
    have hpqPosR : (0 : ℝ) < (p : ℝ) * (q : ℝ) :=
      mul_pos hpPosR hqPosR
    have hpqY : (p : ℝ) * (q : ℝ) ≤ (yNat n : ℝ) ^ 2 := by
      have hnat : p * q ≤ yNat n * yNat n := Nat.mul_le_mul hpY hqY
      exact_mod_cast (by simpa only [pow_two] using hnat)
    have hdelta0 : 0 ≤ delta := by
      dsimp only [delta]
      positivity
    have hdiff :
        |(mu.deleteGuards guards hsmall).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
            mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))| ≤
          4 * delta := by
      have hraw := mu.abs_deleteGuards_expect_sub_le guards hsmall
        (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))
        (show 0 ≤ (1 : ℝ) by norm_num)
        (fun m ↦ by
          rw [abs_of_nonneg (divInd_nonneg _ _)]
          exact divInd_le_one _ _)
      have hperturb := mu.guardPerturbation_le_four_mul_guardMass
        guards hhalf
      exact hraw.trans ((mul_le_mul_of_nonneg_left
        (hperturb.trans (mul_le_mul_of_nonneg_left hmass (by norm_num)))
        (by norm_num)).trans_eq (by ring))
    have habsorb : 4 * delta ≤
        guardSquarefreeError S G K n * pairWeight p q 1 1 := by
      have hmul : 4 * delta * ((p : ℝ) * (q : ℝ)) ≤
          (2 * delta * (yNat n : ℝ) ^ 2) * 4 := by
        have hleft : 4 * delta * ((p : ℝ) * (q : ℝ)) ≤
            4 * delta * (yNat n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hpqY
            (mul_nonneg (by norm_num) hdelta0)
        nlinarith
      unfold guardSquarefreeError pairWeight
      norm_num
      change 4 * delta ≤
        (2 * delta * (yNat n : ℝ) ^ 2) *
          (4 / ((p : ℝ) * (q : ℝ)))
      rw [show (2 * delta * (yNat n : ℝ) ^ 2) *
          (4 / ((p : ℝ) * (q : ℝ))) =
        ((2 * delta * (yNat n : ℝ) ^ 2) * 4) /
          ((p : ℝ) * (q : ℝ)) by ring]
      exact (le_div_iff₀ hpqPosR).2 hmul
    calc
      |(mu.deleteGuards guards hsmall).expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
          paperDivisibilityMain n (pairPower p q 1 1)| ≤
        |(mu.deleteGuards guards hsmall).expect
              (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
            mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))| +
          |mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
            paperDivisibilityMain n (pairPower p q 1 1)| := by
          calc
            _ = |((mu.deleteGuards guards hsmall).expect
                    (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
                  mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))) +
                (mu.expect (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
                  paperDivisibilityMain n (pairPower p q 1 1))| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ guardSquarefreeError S G K n * pairWeight p q 1 1 +
          E * pairWeight p q 1 1 := add_le_add (hdiff.trans habsorb) (hpair p hp q hq)
      _ = (E + guardSquarefreeError S G K n) * pairWeight p q 1 1 := by ring
  · intro p hp
    have hpPrime := prime_of_mem_primeBand hp
    have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hp
    have hyPos : 0 < yNat n := hpPrime.pos.trans_le hpY
    have hpPosR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hpYsq : (p : ℝ) ≤ (yNat n : ℝ) ^ 2 := by
      exact_mod_cast (calc
        p ≤ yNat n := hpY
        _ ≤ yNat n ^ 2 := by nlinarith)
    have hdelta0 : 0 ≤ delta := by
      dsimp only [delta]
      positivity
    have hdiff :
        |(mu.deleteGuards guards hsmall).expect
              (fun m ↦ divInd p (m : ℕ)) -
            mu.expect (fun m ↦ divInd p (m : ℕ))| ≤ 4 * delta := by
      have hraw := mu.abs_deleteGuards_expect_sub_le guards hsmall
        (fun m ↦ divInd p (m : ℕ))
        (show 0 ≤ (1 : ℝ) by norm_num)
        (fun m ↦ by
          rw [abs_of_nonneg (divInd_nonneg _ _)]
          exact divInd_le_one _ _)
      have hperturb := mu.guardPerturbation_le_four_mul_guardMass guards hhalf
      exact hraw.trans ((mul_le_mul_of_nonneg_left
        (hperturb.trans (mul_le_mul_of_nonneg_left hmass (by norm_num)))
        (by norm_num)).trans_eq (by ring))
    have habsorb : 4 * delta ≤
        guardSquarefreeError S G K n * singleWeight p 1 := by
      have hmul : 4 * delta * (p : ℝ) ≤
          (2 * delta * (yNat n : ℝ) ^ 2) * 2 := by
        have hleft : 4 * delta * (p : ℝ) ≤
            4 * delta * (yNat n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hpYsq
            (mul_nonneg (by norm_num) hdelta0)
        nlinarith
      unfold guardSquarefreeError singleWeight
      norm_num
      change 4 * delta ≤
        (2 * delta * (yNat n : ℝ) ^ 2) * (2 / (p : ℝ))
      rw [show (2 * delta * (yNat n : ℝ) ^ 2) * (2 / (p : ℝ)) =
        ((2 * delta * (yNat n : ℝ) ^ 2) * 2) / (p : ℝ) by ring]
      exact (le_div_iff₀ hpPosR).2 hmul
    calc
      |(mu.deleteGuards guards hsmall).expect (fun m ↦ divInd p (m : ℕ)) -
          paperDivisibilityMain n p| ≤
        |(mu.deleteGuards guards hsmall).expect (fun m ↦ divInd p (m : ℕ)) -
            mu.expect (fun m ↦ divInd p (m : ℕ))| +
          |mu.expect (fun m ↦ divInd p (m : ℕ)) -
            paperDivisibilityMain n p| := by
          calc
            _ = |((mu.deleteGuards guards hsmall).expect
                    (fun m ↦ divInd p (m : ℕ)) -
                  mu.expect (fun m ↦ divInd p (m : ℕ))) +
                (mu.expect (fun m ↦ divInd p (m : ℕ)) -
                  paperDivisibilityMain n p)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ guardSquarefreeError S G K n * singleWeight p 1 +
          E * singleWeight p 1 := add_le_add (hdiff.trans habsorb) (hsingle p hp)
      _ = (E + guardSquarefreeError S G K n) * singleWeight p 1 := by ring



end

end Erdos390.Full.GuardDeletionSquarefreeProfiles

end

theorem solution :
∀ (S G : Finset.{0} Nat) (hS : Finset.Nonempty.{0} S) (score : ↥S → Real) (K : Real),
  (∀ (x : ↥S), LE.le.{0} (abs.{0} (score x)) K) →
    ∀ {n W : Nat} {E : Real},
      LE.le.{0}
          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Real.exp (HMul.hMul.{0, 0, 0} (2 : Real) K)) ↑(Finset.card.{0} G))
            ↑(Finset.card.{0} S))
          (1 / 2 : Real) →
        (∀ (p : Nat),
            Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
              ∀ (q : Nat),
                Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.FiniteProbability.expect.{0}
                          (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                            (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) score)
                          fun m =>
                          Erdos390.Full.ArithmeticModel.divInd
                            (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)) ↑m)
                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n
                          (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                    (HMul.hMul.{0, 0, 0} E
                      (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat)))) →
          (∀ (p : Nat),
              Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (Erdos390.Full.FiniteProbability.expect.{0}
                        (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                          (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) score)
                        fun m => Erdos390.Full.ArithmeticModel.divInd p ↑m)
                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n p)))
                  (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
            ∃ (hsmall :
              LT.lt.{0}
                (Erdos390.Full.FiniteProbability.guardMass.{0}
                  (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                    (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) score)
                  (Erdos390.Full.GuardedUniformCell.guardSubtype.{0} S G))
                (1 : Real)),
              have deleted :=
                Erdos390.Full.FiniteProbability.deleteGuards.{0}
                  (Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                    (Erdos390.Full.FiniteProbability.uniformOnFinset.{0} S hS) score)
                  (Erdos390.Full.GuardedUniformCell.guardSubtype.{0} S G) hsmall;
              And
                (∀ (p : Nat),
                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                    ∀ (q : Nat),
                      Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (Erdos390.Full.FiniteProbability.expect.{0} deleted fun m =>
                                Erdos390.Full.ArithmeticModel.divInd
                                  (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)) ↑m)
                              (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n
                                (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                          (HMul.hMul.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0} E
                              (Erdos390.Full.GuardDeletionSquarefreeProfiles.guardSquarefreeError S G K n))
                            (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat))))
                (∀ (p : Nat),
                  Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FiniteProbability.expect.{0} deleted fun m =>
                            Erdos390.Full.ArithmeticModel.divInd p ↑m)
                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n p)))
                      (HMul.hMul.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0} E
                          (Erdos390.Full.GuardDeletionSquarefreeProfiles.guardSquarefreeError S G K n))
                        (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) := by
  exact @Erdos390.Full.GuardDeletionSquarefreeProfiles.exists_deleteGuards_squarefree_profiles
