-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:33:33.149165+00:00
-- url     : https://prove2.me/submissions/97361f36-62a3-4098-80e6-cd5bcda18a27

import Definitions.Def_erdos390_analytic_compact_goals_003
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le_compact


section
universe u_1 u_2
theorem Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le : Erdos390.AnalyticCompactGoal003.{u_1, u_2} := @Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le_compact
end
/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/











theorem headDensity_pos (P : Pattern) : 0 < headDensity P := by
  have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : (0 : ℝ) < (P.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.modulus_ne_zero
  have htot : (0 : ℝ) < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero P.modulus_ne_zero)
  exact mul_pos (one_div_pos.mpr hfactor) (div_pos htot hmod)



/-! ## The common paper-scale main term -/





theorem paperCellDensity_pos (P : Pattern) {A B : ℝ} (hAB : A < B) :
    0 < paperCellDensity P A B := by
  exact mul_pos (mul_pos (headDensity_pos P) (sub_pos.mpr hAB)) rho_U_pos

































/-! ## Normalization algebra -/











end

end Erdos390.Full.PaperScaleMarkedCell

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

/- Source module: Erdos390.Full.PaperGuardCensus -/
section


/-!
# The concrete numerical-guard census used by the smooth bridge

The rough construction has only two kinds of numerical occurrences which can
meet one of the active smooth cells:

* promoted smooth anchors, in `O(y)` slots;
* endpoints (and the possible donor occurrence) of an `O(y)` family of bank
  paths, with at most one component at each geometric scale.

This file represents those occurrences by a literal finite slot type and
defines the numerical guard set as the image of its value map.  Consequently
the guard-cardinality estimate is a theorem about `Finset.image`; it is not a
field of a contract and it is not assumed about an arbitrary finset.

The number of geometric slots is fixed here to `ceil(log n)+1`.  This is a
harmless enlargement of the paper's geometric-scale list and makes the
`O(y log n)` census completely explicit.  Multiple slots are allowed to map to
the same integer; this only makes the proved image-cardinality bound stronger.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability GuardedUniformCell ValuationTiltCell

noncomputable section













/-- The global bridge-relevant guard census, derived from the image
construction rather than postulated. -/
theorem Ledger.card_guards_le {n Cprom Cbank : ℕ}
    (G : Ledger n Cprom Cbank) :
    G.guards.card ≤
      Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 := by
  calc
    G.guards.card ≤ (Finset.univ : Finset (GuardSlot n Cprom Cbank)).card :=
      Finset.card_image_le
    _ = Fintype.card (GuardSlot n Cprom Cbank) := Finset.card_univ
    _ = _ := card_guardSlot n Cprom Cbank

/-- The concrete ceiling has the advertised logarithmic size. -/
theorem cast_scaleSlots_lt {n : ℕ} (hn : 1 ≤ n) :
    (scaleSlots n : ℝ) < L n + 2 := by
  have hL : 0 ≤ L n := by
    unfold L
    exact Real.log_nonneg (by exact_mod_cast hn)
  unfold scaleSlots
  push_cast
  have hceil := Nat.ceil_lt_add_one hL
  linarith

/-- A weak inequality convenient in multiplicative census estimates. -/
theorem cast_scaleSlots_le {n : ℕ} (hn : 1 ≤ n) :
    (scaleSlots n : ℝ) ≤ L n + 2 :=
  (cast_scaleSlots_lt hn).le

/-- Real-cast form of the image census. -/
theorem Ledger.cast_card_guards_le {n Cprom Cbank : ℕ}
    (G : Ledger n Cprom Cbank) (hn : 1 ≤ n) :
    (G.guards.card : ℝ) ≤
      (Cprom + 3 * Cbank * (L n + 2)) * (yNat n : ℝ) := by
  have hcard : (G.guards.card : ℝ) ≤
      (Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 : ℕ) := by
    exact_mod_cast G.card_guards_le
  have hy0 : (0 : ℝ) ≤ (yNat n : ℝ) := by positivity
  have hscale := cast_scaleSlots_le hn
  calc
    (G.guards.card : ℝ) ≤
        (Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 : ℕ) := hcard
    _ = ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (scaleSlots n : ℝ)) *
          (yNat n : ℝ) := by
      push_cast
      ring
    _ ≤ ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
          (yNat n : ℝ) := by
      gcongr
    _ = (Cprom + 3 * Cbank * (L n + 2)) * (yNat n : ℝ) := by ring













end

end Erdos390.Full.PaperGuardCensus

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



/-- The concrete census-to-cell ratio, using the proved raw-cell density. -/
theorem guard_card_div_rawCell_le
    {Head : Type*} [Fintype Head]
    (P : Head → Pattern) (Iphys : PhysicalIntervals)
    {n Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (c : PaperBridgeFit.Cell Head) (hn : 1 ≤ n)
    (hdensity :
      paperCellDensity (P c.1) (Iphys.lower c.2) (Iphys.upper c.2) *
          (n : ℝ) / 2 ≤ (rawCell P Iphys n c).card) :
    (G.guards.card : ℝ) / ((rawCell P Iphys n c).card : ℝ) ≤
      2 * censusRatioMajorant Cprom Cbank n /
        paperCellDensity (P c.1) (Iphys.lower c.2) (Iphys.upper c.2) := by
  let density :=
    paperCellDensity (P c.1) (Iphys.lower c.2) (Iphys.upper c.2)
  have hdensityPos : 0 < density :=
    paperCellDensity_pos (P c.1) (Iphys.lower_lt_upper c.2)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrawPos : 0 < ((rawCell P Iphys n c).card : ℝ) :=
    (div_pos (mul_pos hdensityPos hnR) (by norm_num)).trans_le hdensity
  have hguard := G.cast_card_guards_le hn
  have hyfloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (by omega : 0 < n)).le
  have hcoef : 0 ≤
      (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  have hguardY : (G.guards.card : ℝ) ≤
      ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n :=
    hguard.trans (mul_le_mul_of_nonneg_left hyfloor hcoef)
  have hdivRaw :
      (G.guards.card : ℝ) / ((rawCell P Iphys n c).card : ℝ) ≤
        (G.guards.card : ℝ) / (density * (n : ℝ) / 2) := by
    exact div_le_div_of_nonneg_left (by positivity)
      (div_pos (mul_pos hdensityPos hnR) (by norm_num)) hdensity
  calc
    (G.guards.card : ℝ) / ((rawCell P Iphys n c).card : ℝ) ≤
        (G.guards.card : ℝ) / (density * (n : ℝ) / 2) := hdivRaw
    _ ≤ (((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n) /
          (density * (n : ℝ) / 2) :=
      div_le_div_of_nonneg_right hguardY
        (div_nonneg (mul_nonneg hdensityPos.le hnR.le) (by norm_num))
    _ = 2 * censusRatioMajorant Cprom Cbank n / density := by
      unfold censusRatioMajorant
      field_simp [hdensityPos.ne', hnR.ne']















end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalGuardPowerCorrection -/
section


/-!
# The canonical guard contribution to the prime-power correction row

The prime-power reference law in Lemma 8.4 lives on the unguarded raw
structured cells, whereas the medium-only bridge law lives on the literal
guard-deleted cells.  This file compares the two tagged mixtures without
changing their (post-tilt) component weights.  The comparison includes all
between-component covariance terms.

No arbitrary `BridgeData` is declared canonical.  The finite comparison is
stated under the exact equality between its `sampleData` field and the
canonical constructor from `PaperGuardedStructuredSample`; all dependent
sample-space identifications are then obtained from
`canonicalSampleData_cellFinset`.
-/

open scoped BigOperators
open Filter Topology

set_option maxRecDepth 5000

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw StructuredCells
open PaperGuardCensus GuardedUniformCell
open ValuationScoreDomination

namespace BridgeData



variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)















omit [DecidableEq Head] in theorem canonicalGuardPerturbationConstant_nonneg
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Kscore : ℝ) :
    0 ≤ canonicalGuardPerturbationConstant P I Kscore := by
  unfold canonicalGuardPerturbationConstant
  apply Finset.sum_nonneg
  intro c hc
  exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)).le







/-- Fully concrete finite-`n` guard specialization of the prime-power row.

The hypotheses are precisely the estimates supplied by the canonical raw
cells: a pointwise bound for the actual medium score, the literal half-mass
census inequality, the proved raw-cell density, and a logarithmic valuation
envelope.  The conclusion keeps the actual post-tilt component weights.  In
particular, no comparison with an arbitrarily chosen mixture is hidden in the
statement. -/
theorem weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) {Cprom Cbank : ℕ}
    (G : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ G.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W) P I G hsep hremaining)
    (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (hW : 1 < B.sampleData.W)
    {Kscore Cenv : ℝ} (hCenv : 0 ≤ Cenv)
    (hscore : ∀ c : Cell Head,
      ∀ m : rawCell P I B.sampleData.n c,
        |valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore)
    (hsmallCensus : ∀ c : Cell Head,
      Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
        ((rawCell P I B.sampleData.n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (hdensity : ∀ c : Cell Head,
      PaperScaleMarkedCell.paperCellDensity
          (P c.1) (I.lower c.2) (I.upper c.2) *
          (B.sampleData.n : ℝ) / 2 ≤
        (rawCell P I B.sampleData.n c).card)
    (hEnvelope : ∀ c : Cell Head,
      valuationEnvelope I B.sampleData.n B.sampleData.W c ≤
        Cenv * Scale.L B.sampleData.n)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (p.1 : ℝ) *
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
          ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
              (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covVV p.1 q.1 -
            (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
              (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covII p.1 q.1)| ≤
      guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
        (canonicalGuardPerturbationConstant P I Kscore) B.sampleData.n := by
  let census := PaperGuardCensus.censusRatioMajorant
    Cprom Cbank B.sampleData.n
  let Dguard := canonicalGuardPerturbationConstant P I Kscore
  let hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty :=
    fun c ↦ (hremaining c).mono Finset.sdiff_subset
  let score : ∀ c : Cell Head, rawCell P I B.sampleData.n c → ℝ :=
    fun _ m ↦ valuationScore
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  have hn : 1 ≤ B.sampleData.n := B.n_gt_one.le
  have hnpos : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hcensus0 : 0 ≤ census := by
    dsimp only [census]
    unfold PaperGuardCensus.censusRatioMajorant
    have hL0 : 0 ≤ Scale.L B.sampleData.n :=
      Real.log_nonneg (by exact_mod_cast hn)
    have hcoef : 0 ≤ (Cprom : ℝ) +
        3 * (Cbank : ℝ) * (Scale.L B.sampleData.n + 2) := by
      positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos hnpos).le) (by positivity)
  have hDguard0 : 0 ≤ Dguard := by
    simpa only [Dguard] using
      canonicalGuardPerturbationConstant_nonneg P I Kscore
  have hsmall : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (score c)).guardMass
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1) := by
    intro c
    let mu := (uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
      (score c)
    let guards := guardSubtype (rawCell P I B.sampleData.n c) G.guards
    have hmass : mu.guardMass guards ≤
        Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
          ((rawCell P I B.sampleData.n c).card : ℝ) := by
      simpa only [mu, guards, score, hS] using
        tilted_uniform_guardMass_le
          (rawCell P I B.sampleData.n c) G.guards (hS c) (score c)
          Kscore (by simpa only [score] using hscore c)
    have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 :=
      hmass.trans (hsmallCensus c)
    exact hhalf.trans_lt (by norm_num)
  have hperturb : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P I B.sampleData.n c) (hS c)).exponentialTilt
        (score c)).guardPerturbation
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) ≤
          Dguard * census) := by
    intro c
    let S := rawCell P I B.sampleData.n c
    let mu := (uniformOnFinset S (hS c)).exponentialTilt (score c)
    let guards := guardSubtype S G.guards
    let density := PaperScaleMarkedCell.paperCellDensity
      (P c.1) (I.lower c.2) (I.upper c.2)
    have hdensityPos : 0 < density := by
      exact PaperScaleMarkedCell.paperCellDensity_pos
        (P c.1) (I.lower_lt_upper c.2)
    have hratio : (G.guards.card : ℝ) / (S.card : ℝ) ≤
        2 * census / density := by
      simpa only [S, census] using
        guard_card_div_rawCell_le P I G c hn (hdensity c)
    have hmass : mu.guardMass guards ≤
        Real.exp (2 * Kscore) * (G.guards.card : ℝ) / (S.card : ℝ) := by
      simpa only [mu, guards, S, score, hS] using
        tilted_uniform_guardMass_le S G.guards (hS c) (score c)
          Kscore (by simpa only [score] using hscore c)
    have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 := by
      exact hmass.trans (by simpa only [S] using hsmallCensus c)
    have hperturbMass :=
      mu.guardPerturbation_le_four_mul_guardMass guards hhalf
    have hcellConstant :
        8 * Real.exp (2 * Kscore) / density ≤ Dguard := by
      have hsingle :
          8 * Real.exp (2 * Kscore) /
              PaperScaleMarkedCell.paperCellDensity
                (P c.1) (I.lower c.2) (I.upper c.2) ≤
            ∑ c' : Cell Head,
              8 * Real.exp (2 * Kscore) /
                PaperScaleMarkedCell.paperCellDensity
                  (P c'.1) (I.lower c'.2) (I.upper c'.2) :=
        Finset.single_le_sum
          (fun c' hc' ↦ div_nonneg
            (mul_nonneg (by norm_num) (Real.exp_pos _).le)
            (PaperScaleMarkedCell.paperCellDensity_pos
              (P c'.1) (I.lower_lt_upper c'.2)).le)
          (Finset.mem_univ c)
      simpa only [Dguard, canonicalGuardPerturbationConstant, density] using hsingle
    have hmassRatio : mu.guardMass guards ≤
        Real.exp (2 * Kscore) * (2 * census / density) := by
      calc
        mu.guardMass guards ≤
            Real.exp (2 * Kscore) * (G.guards.card : ℝ) /
              (S.card : ℝ) := hmass
        _ = Real.exp (2 * Kscore) *
              ((G.guards.card : ℝ) / (S.card : ℝ)) := by ring
        _ ≤ Real.exp (2 * Kscore) * (2 * census / density) :=
          mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
    calc
      mu.guardPerturbation guards ≤ 4 * mu.guardMass guards := hperturbMass
      _ ≤ 4 * (Real.exp (2 * Kscore) * (2 * census / density)) :=
        mul_le_mul_of_nonneg_left hmassRatio (by norm_num)
      _ = (8 * Real.exp (2 * Kscore) / density) * census := by ring
      _ ≤ Dguard * census :=
        mul_le_mul_of_nonneg_right hcellConstant hcensus0
  have hrow :=
    B.sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
      P I Cmax G hsep hremaining hcanonical xi hC_le hW
      (K := Cenv * Scale.L B.sampleData.n) (d := Dguard * census)
      (mul_nonneg hCenv B.L_pos.le) (mul_nonneg hDguard0 hcensus0)
      hEnvelope
      (by simpa only [hS, score] using hsmall)
      (by simpa only [hS, score] using hperturb) p
  have hpY : (p.1 : ℝ) ≤ (yNat B.sampleData.n : ℝ) := by
    exact_mod_cast le_yNat_of_mem_primeBand p.2
  have hsum0 : 0 ≤
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
          ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
            (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| :=
    Finset.sum_nonneg fun q hq ↦ abs_nonneg _
  calc
    (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
            ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
              (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| ≤
      (yNat B.sampleData.n : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
            ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
              (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| :=
        mul_le_mul_of_nonneg_right hpY hsum0
    _ ≤ (yNat B.sampleData.n : ℝ) *
        PaperGuardCensus.guardPowerCorrectionRowError
          (Cenv * Scale.L B.sampleData.n) (Dguard * census) :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv Dguard
        B.sampleData.n := by
      rfl













end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3)
  [inst_4 : Nonempty.{u_1 + 1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cmax : Real) {Cprom Cbank : Nat}
  (G :
    Erdos390.Full.PaperGuardCensus.Ledger
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
      Cprom Cbank)
  (hsep :
    @LT.lt.{0} Nat instLTNat
      (Erdos390.Full.ArithmeticModel.physicalBound (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)))
      (Erdos390.Full.ArithmeticModel.physicalBound (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))))
  (hremaining :
    ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
      @Finset.Nonempty.{0} Nat
        (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
            c)
          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
            Cprom Cbank G))),
  @Eq.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head inst)
      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
      (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Head inst P I
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
        Cprom Cbank G hsep hremaining) →
    ∀ (xi : @Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
      (hC_le : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LE.le.{0} Real Real.instLE (I.upper sigma) Cmax),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)) →
        ∀ {Kscore Cenv : Real},
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Cenv →
            (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                (m :
                  @Subtype.{1} Nat fun (x : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))
                        c)
                      x),
                @LE.le.{0} Real Real.instLE
                  (@abs.{0} Real Real.lattice Real.instAddGroup
                    (Erdos390.Full.ValuationScoreDomination.valuationScore
                      (Erdos390.Full.ArithmeticModel.primeBand
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveNatCoefficient.{u_1, u_2} Head Band inst inst_1
                        inst_2 inst_3 B xi)
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
                      (@Subtype.val.{1} Nat
                        (fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            x)
                        m)))
                  Kscore) →
              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  @LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (Real.exp
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            Kscore))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              Cprom Cbank G))))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Finset.card.{0} Nat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                    @LE.le.{0} Real Real.instLE
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (Erdos390.Full.PaperScaleMarkedCell.paperCellDensity
                            (P (@Prod.fst.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))
                            (I.lower (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))
                            (I.upper (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c)))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))))
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Finset.card.{0} Nat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c)))) →
                  (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                      @LE.le.{0} Real Real.instLE
                        (@Erdos390.Full.PaperGuardCensus.valuationEnvelope.{u_1} Head inst I
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))
                          c)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Cenv
                          (Erdos390.Full.Scale.L
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))))) →
                    ∀
                      (p :
                        Erdos390.Full.ArithmeticBandGeometry.BandPrime
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))),
                      @LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@Subtype.val.{1} Nat
                              (fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (Erdos390.Full.ArithmeticModel.primeBand
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B)))
                                  p)
                              p))
                          (@Finset.sum.{0, 0}
                            (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B)))
                            Real Real.instAddCommMonoid
                            (@Finset.univ.{0}
                              (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B)))
                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.instFintypeBandPrime
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))))
                            fun
                              (q :
                                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))) =>
                            @abs.{0} Real Real.lattice Real.instAddGroup
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                  (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B)
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardedMediumReferenceLaw.{u_1,
                                          u_2}
                                      Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                    (@Subtype.val.{1} Nat
                                      (fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (Erdos390.Full.ArithmeticModel.primeBand
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)))
                                          p)
                                      p)
                                    (@Subtype.val.{1} Nat
                                      (fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (Erdos390.Full.ArithmeticModel.primeBand
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)))
                                          p)
                                      q))
                                  (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B)
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardedMediumReferenceLaw.{u_1,
                                          u_2}
                                      Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                    (@Subtype.val.{1} Nat
                                      (fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (Erdos390.Full.ArithmeticModel.primeBand
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)))
                                          p)
                                      p)
                                    (@Subtype.val.{1} Nat
                                      (fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (Erdos390.Full.ArithmeticModel.primeBand
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)))
                                          p)
                                      q)))
                                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                  (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                    (@Sigma.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                      fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Subtype.{1} Nat fun (x : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          x)
                                    (@Sigma.instFintype.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                      (fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                        @Subtype.{1} Nat fun (x : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                  Band inst inst_1 inst_2 inst_3 B))
                                              c)
                                            x)
                                      (fun (i : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                        @Finset.Subtype.fintype.{0} Nat
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            i))
                                      (@instFintypeProd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign inst
                                        Erdos390.Full.PaperBridgeFit.instFintypePhysicalSign))
                                    (Erdos390.Full.ArithmeticModel.physicalBound Cmax
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B)))
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalRawMediumReferenceLaw.{u_1, u_2}
                                      Head Band inst inst_1 inst_2 inst_3 B inst_4 P I Cmax xi hC_le
                                      fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Finset.Nonempty.mono.{0} Nat
                                        (@SDiff.sdiff.{0} (Finset.{0} Nat)
                                          (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            Cprom Cbank G))
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            Cprom Cbank G))
                                        (hremaining c))
                                    (@Subtype.val.{1} Nat
                                      (fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (Erdos390.Full.ArithmeticModel.primeBand
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)))
                                          p)
                                      p)
                                    (@Subtype.val.{1} Nat
                                      (fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (Erdos390.Full.ArithmeticModel.primeBand
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)))
                                          p)
                                      q))
                                  (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                    (@Sigma.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                      fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Subtype.{1} Nat fun (x : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          x)
                                    (@Sigma.instFintype.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                      (fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                        @Subtype.{1} Nat fun (x : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                  Band inst inst_1 inst_2 inst_3 B))
                                              c)
                                            x)
                                      (fun (i : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                        @Finset.Subtype.fintype.{0} Nat
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            i))
                                      (@instFintypeProd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign inst
                                        Erdos390.Full.PaperBridgeFit.instFintypePhysicalSign))
                                    (Erdos390.Full.ArithmeticModel.physicalBound Cmax
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B)))
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalRawMediumReferenceLaw.{u_1, u_2}
                                      Head Band inst inst_1 inst_2 inst_3 B inst_4 P I Cmax xi hC_le
                                      fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Finset.Nonempty.mono.{0} Nat
                                        (@SDiff.sdiff.{0} (Finset.{0} Nat)
                                          (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            Cprom Cbank G))
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            Cprom Cbank G))
                                        (hremaining c))
                                    (@Subtype.val.{1} Nat
                                      (fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (Erdos390.Full.ArithmeticModel.primeBand
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)))
                                          p)
                                      p)
                                    (@Subtype.val.{1} Nat
                                      (fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (Erdos390.Full.ArithmeticModel.primeBand
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)))
                                          p)
                                      q))))))
                        (Erdos390.Full.PaperBridgeFit.BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardPerturbationConstant.{u_1} Head inst P
                            I Kscore)
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
