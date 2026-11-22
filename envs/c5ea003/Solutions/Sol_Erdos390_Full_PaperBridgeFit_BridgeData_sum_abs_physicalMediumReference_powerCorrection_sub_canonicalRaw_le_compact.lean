-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:04:38.218718+00:00
-- url     : https://prove2.me/submissions/c126fff9-de8c-45d7-a973-4b0652423ce9

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
import Theorems.Thm_Erdos390_Full_PaperGuardCensus_sum_abs_guardDeleted_powerCorrectionRow_sub_le

/- Source module: Erdos390.Full.PaperBridgeNuisanceTiltFallback -/
section


/-!
# Marked fallback through the physical/head bridge tilt

On a fixed tagged bridge cell all centered-head coordinates are constant.
Consequently the residual nuisance tilt is exactly a small physical-log tilt;
the constant head factor cancels from normalization.  We combine that exact
identity with reciprocal divisibility bounds for the medium-prime tilt.

The resulting estimates retain the marked `1 / D` and `1 / (p q)` scales.
No total-variation estimate is used.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination OmittedTiltFallback
open DivisibilityMomentBounds

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)





/-- On a literal cell, the medium part of the bridge score is the genuine
valuation score used by the structured-cell estimates. -/
theorem sigmaCellScore_scaledMedium_eq_valuationScore [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledMediumScore xi) c m =
      valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L m := by
  unfold sigmaCellScore scaledMediumScore valuationScore
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ (B.effectiveNatCoefficient xi p / B.L) * valuation p m)
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.effectiveNatCoefficient_of_mem xi p.2]
  simp only [StructuredSampleData.value]































end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.GuardDeletionReindexing -/
section


/-!
# Exact reindexing after guard deletion

The guard perturbation lemmas use a probability law on the original cell,
with deleted points assigned mass zero.  The bridge uses the subtype of the
literal guard-deleted finset.  This file proves that these are exactly the
same conditional law after reindexing, including after an exponential tilt.
-/

open scoped BigOperators

namespace Erdos390.Full.GuardedUniformCell

open FiniteProbability

noncomputable section

variable {Alpha : Type*} [DecidableEq Alpha]









/-- A sum over non-guard members of the original subtype is exactly the
corresponding sum over the literal difference finset subtype. -/
theorem sum_complement_guard_eq_sum_remaining
    (S G : Finset Alpha) (F : S → ℝ) :
    ∑ x ∈ ((Finset.univ : Finset S) \ guardSubtype S G), F x =
      ∑ y : ↑(S \ G), F (remainingEmbedding S G y) := by
  rw [Finset.sum_subtype
    (p := fun x : ↑S ↦ x ∉ guardSubtype S G)
    ((Finset.univ : Finset S) \ guardSubtype S G)
    (fun x ↦ by simp)]
  symm
  exact Fintype.sum_equiv (remainingEquiv S G)
    (fun y ↦ F (remainingEmbedding S G y))
    (fun x ↦ F x.1) (fun _ ↦ rfl)



theorem remainingExpSum_pos (S G : Finset Alpha)
    (hR : (S \ G).Nonempty) (score : ↑S → ℝ) :
    0 < remainingExpSum S G score := by
  obtain ⟨a, ha⟩ := hR
  let x : ↑(S \ G) := ⟨a, ha⟩
  unfold remainingExpSum
  exact Finset.sum_pos (fun y hy ↦ Real.exp_pos _) ⟨x, Finset.mem_univ x⟩

/-- Partition function of the uniformly weighted remaining subtype. -/
theorem uniform_remaining_expPartition_eq
    (S G : Finset Alpha) (hR : (S \ G).Nonempty)
    (score : ↑S → ℝ) :
    (uniformOnFinset (S \ G) hR).expPartition
        (fun y ↦ score (remainingEmbedding S G y)) =
      (1 / ((S \ G).card : ℝ)) * remainingExpSum S G score := by
  unfold FiniteProbability.expPartition FiniteProbability.expect
    remainingExpSum
  simp only [uniformOnFinset_mass]
  rw [Finset.mul_sum]

/-- Exact remaining mass of a tilted uniform law, expressed through the
same exponential sum as the literal difference-finset law. -/
theorem one_sub_tilted_guardMass_eq
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : ↑S → ℝ) :
    1 - ((uniformOnFinset S hS).exponentialTilt score).guardMass
        (guardSubtype S G) =
      (1 / (S.card : ℝ) /
          (uniformOnFinset S hS).expPartition score) *
        remainingExpSum S G score := by
  let mu := (uniformOnFinset S hS).exponentialTilt score
  rw [← mu.sum_mass_complement_guard (guardSubtype S G)]
  rw [sum_complement_guard_eq_sum_remaining]
  unfold mu FiniteProbability.exponentialTilt
  simp only [uniformOnFinset_mass]
  unfold remainingExpSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Pointwise equality of the conditional tilted mass on every surviving
point and the tilted uniform mass on the literal difference finset. -/
theorem deleteGuards_tilted_uniform_mass_remaining_eq
    (S G : Finset Alpha) (hS : S.Nonempty) (hR : (S \ G).Nonempty)
    (score : ↑S → ℝ)
    (hsmall : ((uniformOnFinset S hS).exponentialTilt score).guardMass
      (guardSubtype S G) < 1)
    (y : ↑(S \ G)) :
    (((uniformOnFinset S hS).exponentialTilt score).deleteGuards
        (guardSubtype S G) hsmall).mass (remainingEmbedding S G y) =
      ((uniformOnFinset (S \ G) hR).exponentialTilt
        (fun z ↦ score (remainingEmbedding S G z))).mass y := by
  rw [FiniteProbability.deleteGuards_mass_of_not_mem _ _ _
    (remainingEmbedding_not_guard S G y)]
  rw [one_sub_tilted_guardMass_eq]
  unfold FiniteProbability.exponentialTilt
  simp only [uniformOnFinset_mass]
  rw [uniform_remaining_expPartition_eq]
  have hScard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have hRcard : ((S \ G).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hR
  have hZS : (uniformOnFinset S hS).expPartition score ≠ 0 :=
    ne_of_gt ((uniformOnFinset S hS).expPartition_pos score)
  have hA : remainingExpSum S G score ≠ 0 :=
    ne_of_gt (remainingExpSum_pos S G hR score)
  field_simp [hScard, hRcard, hZS, hA]

/-- Exact expectation reindexing between the same two probability laws. -/
theorem deleteGuards_tilted_uniform_expect_remaining_eq
    (S G : Finset Alpha) (hS : S.Nonempty) (hR : (S \ G).Nonempty)
    (score : ↑S → ℝ)
    (hsmall : ((uniformOnFinset S hS).exponentialTilt score).guardMass
      (guardSubtype S G) < 1)
    (F : ↑S → ℝ) :
    (((uniformOnFinset S hS).exponentialTilt score).deleteGuards
        (guardSubtype S G) hsmall).expect F =
      ((uniformOnFinset (S \ G) hR).exponentialTilt
        (fun z ↦ score (remainingEmbedding S G z))).expect
          (fun z ↦ F (remainingEmbedding S G z)) := by
  let mu := ((uniformOnFinset S hS).exponentialTilt score).deleteGuards
    (guardSubtype S G) hsmall
  let nu := (uniformOnFinset (S \ G) hR).exponentialTilt
    (fun z ↦ score (remainingEmbedding S G z))
  have hguard :
      ∑ x ∈ guardSubtype S G, mu.mass x * F x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [FiniteProbability.deleteGuards_mass_of_mem]
    · simp
    · exact hx
  have hsplit := Finset.sum_sdiff
    (Finset.subset_univ (guardSubtype S G))
    (f := fun x ↦ mu.mass x * F x)
  rw [hguard, add_zero] at hsplit
  unfold FiniteProbability.expect
  calc
    (∑ x : ↑S, mu.mass x * F x) =
        ∑ x ∈ ((Finset.univ : Finset S) \ guardSubtype S G),
          mu.mass x * F x := hsplit.symm
    _ = ∑ y : ↑(S \ G),
          mu.mass (remainingEmbedding S G y) *
            F (remainingEmbedding S G y) :=
      sum_complement_guard_eq_sum_remaining S G
        (fun x ↦ mu.mass x * F x)
    _ = ∑ y : ↑(S \ G),
          nu.mass y * F (remainingEmbedding S G y) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [show mu.mass (remainingEmbedding S G y) = nu.mass y by
        exact deleteGuards_tilted_uniform_mass_remaining_eq
          S G hS hR score hsmall y]
    _ = ∑ y : ↑(S \ G),
          nu.mass y * F (remainingEmbedding S G y) := rfl



end

end Erdos390.Full.GuardedUniformCell

end

/- Source module: Erdos390.Full.PaperBridgeMediumValuationMixture -/
section


/-!
# The bounded medium-only bridge mixture

The reference law used after guard deletion has the same literal integer
values as the bridge sample and differs from the actual component law only by
the residual physical tilt.  This file records that law with the paper's
common endpoint and proves the exact `VV-II = JI+IJ+JJ` identities used by
the physical-transfer ledger.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







/-- The bounded-law and raw finite-probability definitions of the
prime-power correction are definitionally the same. -/
theorem powerCorrectionCovariance_eq_covVV_sub_covII
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (p q : ℕ) :
    PaperGuardCensus.powerCorrectionCovariance
        law.probability law.value p q =
      law.covVV p q - law.covII p q := rfl







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.FiniteProbabilityMixtureGuardReindexing -/
section


/-!
# Exact guard reindexing for tagged mixtures

Guard perturbation estimates are most naturally stated on the original cell,
where deleted points have mass zero.  The bridge is carried by the literal
difference-finset subtype.  This file lifts the exact component reindexing to
an arbitrary tagged mixture, including its between-component covariance.
-/

namespace Erdos390.Full.GuardedUniformCell

open FiniteProbability

noncomputable section

variable {Cell Alpha : Type*} [Fintype Cell] [DecidableEq Alpha]

/-- Exact expectation reindexing after componentwise guard deletion and
arbitrary common mixing. -/
theorem sigmaMixture_deleteGuards_expect_remaining_eq
    (S G : Cell → Finset Alpha)
    (hS : ∀ c, (S c).Nonempty) (hR : ∀ c, (S c \ G c).Nonempty)
    (score : ∀ c, S c → ℝ)
    (hsmall : ∀ c,
      ((uniformOnFinset (S c) (hS c)).exponentialTilt (score c)).guardMass
        (guardSubtype (S c) (G c)) < 1)
    (weight : FiniteProbability Cell)
    (F : ∀ c, S c → ℝ) :
    let raw : ∀ c, FiniteProbability (S c) := fun c ↦
      (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
    let deleted : ∀ c, FiniteProbability (S c) := fun c ↦
      (raw c).deleteGuards (guardSubtype (S c) (G c)) (hsmall c)
    let remaining : ∀ c, FiniteProbability ↑(S c \ G c) := fun c ↦
      (uniformOnFinset (S c \ G c) (hR c)).exponentialTilt
        (fun z ↦ score c (remainingEmbedding (S c) (G c) z))
    (sigmaMixture weight deleted).expect (fun x ↦ F x.1 x.2) =
      (sigmaMixture weight remaining).expect
        (fun x ↦ F x.1 (remainingEmbedding (S x.1) (G x.1) x.2)) := by
  dsimp only
  rw [sigmaMixture_expect, sigmaMixture_expect]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  exact deleteGuards_tilted_uniform_expect_remaining_eq
    (S c) (G c) (hS c) (hR c) (score c) (hsmall c) (F c)

/-- Exact covariance reindexing for the complete tagged mixture. -/
theorem sigmaMixture_deleteGuards_covariance_remaining_eq
    (S G : Cell → Finset Alpha)
    (hS : ∀ c, (S c).Nonempty) (hR : ∀ c, (S c \ G c).Nonempty)
    (score : ∀ c, S c → ℝ)
    (hsmall : ∀ c,
      ((uniformOnFinset (S c) (hS c)).exponentialTilt (score c)).guardMass
        (guardSubtype (S c) (G c)) < 1)
    (weight : FiniteProbability Cell)
    (F H : ∀ c, S c → ℝ) :
    let raw : ∀ c, FiniteProbability (S c) := fun c ↦
      (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
    let deleted : ∀ c, FiniteProbability (S c) := fun c ↦
      (raw c).deleteGuards (guardSubtype (S c) (G c)) (hsmall c)
    let remaining : ∀ c, FiniteProbability ↑(S c \ G c) := fun c ↦
      (uniformOnFinset (S c \ G c) (hR c)).exponentialTilt
        (fun z ↦ score c (remainingEmbedding (S c) (G c) z))
    (sigmaMixture weight deleted).covariance
        (fun x ↦ F x.1 x.2) (fun x ↦ H x.1 x.2) =
      (sigmaMixture weight remaining).covariance
        (fun x ↦ F x.1 (remainingEmbedding (S x.1) (G x.1) x.2))
        (fun x ↦ H x.1 (remainingEmbedding (S x.1) (G x.1) x.2)) := by
  dsimp only
  unfold FiniteProbability.covariance
  rw [sigmaMixture_deleteGuards_expect_remaining_eq
      S G hS hR score hsmall weight F,
    sigmaMixture_deleteGuards_expect_remaining_eq
      S G hS hR score hsmall weight H]
  let FH : ∀ c, S c → ℝ := fun c x ↦ F c x * H c x
  have hFH := sigmaMixture_deleteGuards_expect_remaining_eq
    S G hS hR score hsmall weight FH
  dsimp only [FH] at hFH
  rw [hFH]

end

end Erdos390.Full.GuardedUniformCell

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

private theorem sigmaMixture_tilt_covariance_eq_of_finset_family_eq
    {Cell₀ : Type*} [Fintype Cell₀]
    (S T : Cell₀ → Finset ℕ) (hST : S = T)
    (hS : ∀ c, (S c).Nonempty) (hT : ∀ c, (T c).Nonempty)
    (scoreS : ∀ c, S c → ℝ) (scoreT : ∀ c, T c → ℝ)
    (hscore : ∀ c (x : S c) (y : T c),
      (x : ℕ) = (y : ℕ) → scoreS c x = scoreT c y)
    (weight : FiniteProbability Cell₀) (F H : ℕ → ℝ) :
    (sigmaMixture weight (fun c ↦
        (uniformOnFinset (S c) (hS c)).exponentialTilt (scoreS c))).covariance
        (fun x ↦ F (x.2 : ℕ)) (fun x ↦ H (x.2 : ℕ)) =
      (sigmaMixture weight (fun c ↦
        (uniformOnFinset (T c) (hT c)).exponentialTilt (scoreT c))).covariance
        (fun x ↦ F (x.2 : ℕ)) (fun x ↦ H (x.2 : ℕ)) := by
  subst T
  have hscoreEq : scoreS = scoreT := by
    funext c x
    exact hscore c x x rfl
  subst scoreT
  have hproof : hS = hT := Subsingleton.elim _ _
  subst hT
  rfl

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-- Exact canonical guard comparison.  The equality `hcanonical` is the
only place where the abstract bridge data is identified with the canonical
constructor.  In particular, the actual partition-function-reweighted
component weights are retained on both sides. -/
theorem sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
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
    {K d : ℝ} (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hEnvelope : ∀ c : Cell Head,
      valuationEnvelope I B.sampleData.n B.sampleData.W c ≤ K)
    (hsmall : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P I B.sampleData.n c)
          ((hremaining c).mono (Finset.sdiff_subset))).exponentialTilt
        (fun m ↦ valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ))).guardMass
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) < 1))
    (hperturb : ∀ c : Cell Head,
      (((uniformOnFinset (rawCell P I B.sampleData.n c)
          ((hremaining c).mono (Finset.sdiff_subset))).exponentialTilt
        (fun m ↦ valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ))).guardPerturbation
        (guardSubtype (rawCell P I B.sampleData.n c) G.guards) ≤ d))
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
        ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
            (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covVV p.1 q.1 -
          (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
            (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covII p.1 q.1)| ≤
      PaperGuardCensus.guardPowerCorrectionRowError K d := by
  let hS : ∀ c : Cell Head, (rawCell P I B.sampleData.n c).Nonempty :=
    fun c ↦ (hremaining c).mono Finset.sdiff_subset
  let score : ∀ c : Cell Head, rawCell P I B.sampleData.n c → ℝ :=
    fun _ m ↦ valuationScore
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hguard := PaperGuardCensus.sum_abs_guardDeleted_powerCorrectionRow_sub_le
    P I hW G.guards hS score weight p
      hK hd hEnvelope (by simpa only [hS, score] using hsmall)
      (by simpa only [hS, score] using hperturb)
  let S := fun c : Cell Head ↦ rawCell P I B.sampleData.n c
  let guards := fun _c : Cell Head ↦ G.guards
  let mu : ∀ c, FiniteProbability (S c) := fun c ↦
    (uniformOnFinset (S c) (hS c)).exponentialTilt (score c)
  let Gsub : ∀ c, Finset (S c) := fun c ↦
    guardSubtype (S c) G.guards
  let nu : ∀ c, FiniteProbability (S c) := fun c ↦
    (mu c).deleteGuards (Gsub c) (by
      simpa only [mu, Gsub, S, hS, score] using hsmall c)
  have hcellEq (c : Cell Head) :
      B.sampleData.cellFinset c =
        rawCell P I B.sampleData.n c \ G.guards := by
    calc
      B.sampleData.cellFinset c =
          (canonicalSampleData (W := B.sampleData.W)
            P I G hsep hremaining).cellFinset c :=
        congrArg (fun D : StructuredSampleData Head ↦ D.cellFinset c)
          hcanonical
      _ = rawCell P I B.sampleData.n c \ G.guards :=
        canonicalSampleData_cellFinset P I G hsep hremaining c
  have hfamilyEq :
      (fun c : Cell Head ↦ rawCell P I B.sampleData.n c \ G.guards) =
        B.sampleData.cellFinset := by
    funext c
    exact (hcellEq c).symm
  have hreindex (a b : ℕ) :
      (sigmaMixture weight nu).covariance
          (fun x ↦ valuation a (x.2 : ℕ))
          (fun x ↦ valuation b (x.2 : ℕ)) =
        (B.canonicalGuardedMediumReferenceLaw xi).probability.covariance
          (fun x ↦ valuation a
            ((B.canonicalGuardedMediumReferenceLaw xi).value x))
          (fun x ↦ valuation b
            ((B.canonicalGuardedMediumReferenceLaw xi).value x)) := by
    have hraw := sigmaMixture_deleteGuards_covariance_remaining_eq
      S (fun _c : Cell Head ↦ G.guards) hS hremaining score
        (by simpa only [S, hS, score] using hsmall) weight
        (fun _c m ↦ valuation a (m : ℕ))
        (fun _c m ↦ valuation b (m : ℕ))
    have hraw' : (sigmaMixture weight nu).covariance
          (fun x ↦ valuation a (x.2 : ℕ))
          (fun x ↦ valuation b (x.2 : ℕ)) =
        (sigmaMixture weight (fun c ↦
          (uniformOnFinset (S c \ G.guards) (hremaining c)).exponentialTilt
            (fun z ↦ score c (remainingEmbedding (S c) G.guards z)))).covariance
          (fun x ↦ valuation a (x.2 : ℕ))
          (fun x ↦ valuation b (x.2 : ℕ)) := by
      simpa only [S, hS, score, weight, mu, Gsub, nu,
        remainingEmbedding_value] using hraw
    have hremainingMedium :=
      sigmaMixture_tilt_covariance_eq_of_finset_family_eq
        (fun c : Cell Head ↦ S c \ G.guards)
        B.sampleData.cellFinset hfamilyEq hremaining
        B.sampleData.cell_nonempty
        (fun c z ↦ score c (remainingEmbedding (S c) G.guards z))
        (fun c ↦ sigmaCellScore (B.scaledMediumScore xi) c)
        (by
          intro c x y hxy
          change score c (remainingEmbedding (S c) G.guards x) =
            sigmaCellScore (B.scaledMediumScore xi) c y
          rw [B.sigmaCellScore_scaledMedium_eq_valuationScore xi c y]
          dsimp only [score]
          rw [remainingEmbedding_value, hxy])
        weight (valuation a) (valuation b)
    have htarget :
        (sigmaMixture weight (fun c ↦ B.cellMediumLaw xi c)).covariance
            (fun x ↦ valuation a (x.2 : ℕ))
            (fun x ↦ valuation b (x.2 : ℕ)) =
          (B.canonicalGuardedMediumReferenceLaw xi).probability.covariance
            (fun x ↦ valuation a
              ((B.canonicalGuardedMediumReferenceLaw xi).value x))
            (fun x ↦ valuation b
              ((B.canonicalGuardedMediumReferenceLaw xi).value x)) := by
      rfl
    exact hraw'.trans (hremainingMedium.trans htarget)
  have hreindexI (a b : ℕ) :
      (sigmaMixture weight nu).covariance
          (fun x ↦ divInd a (x.2 : ℕ))
          (fun x ↦ divInd b (x.2 : ℕ)) =
        (B.canonicalGuardedMediumReferenceLaw xi).probability.covariance
          (fun x ↦ divInd a
            ((B.canonicalGuardedMediumReferenceLaw xi).value x))
          (fun x ↦ divInd b
            ((B.canonicalGuardedMediumReferenceLaw xi).value x)) := by
    have hraw := sigmaMixture_deleteGuards_covariance_remaining_eq
      S (fun _c : Cell Head ↦ G.guards) hS hremaining score
        (by simpa only [S, hS, score] using hsmall) weight
        (fun _c m ↦ divInd a (m : ℕ))
        (fun _c m ↦ divInd b (m : ℕ))
    have hraw' : (sigmaMixture weight nu).covariance
          (fun x ↦ divInd a (x.2 : ℕ))
          (fun x ↦ divInd b (x.2 : ℕ)) =
        (sigmaMixture weight (fun c ↦
          (uniformOnFinset (S c \ G.guards) (hremaining c)).exponentialTilt
            (fun z ↦ score c (remainingEmbedding (S c) G.guards z)))).covariance
          (fun x ↦ divInd a (x.2 : ℕ))
          (fun x ↦ divInd b (x.2 : ℕ)) := by
      simpa only [S, hS, score, weight, mu, Gsub, nu,
        remainingEmbedding_value] using hraw
    have hremainingMedium :=
      sigmaMixture_tilt_covariance_eq_of_finset_family_eq
        (fun c : Cell Head ↦ S c \ G.guards)
        B.sampleData.cellFinset hfamilyEq hremaining
        B.sampleData.cell_nonempty
        (fun c z ↦ score c (remainingEmbedding (S c) G.guards z))
        (fun c ↦ sigmaCellScore (B.scaledMediumScore xi) c)
        (by
          intro c x y hxy
          change score c (remainingEmbedding (S c) G.guards x) =
            sigmaCellScore (B.scaledMediumScore xi) c y
          rw [B.sigmaCellScore_scaledMedium_eq_valuationScore xi c y]
          dsimp only [score]
          rw [remainingEmbedding_value, hxy])
        weight (divInd a) (divInd b)
    have htarget :
        (sigmaMixture weight (fun c ↦ B.cellMediumLaw xi c)).covariance
            (fun x ↦ divInd a (x.2 : ℕ))
            (fun x ↦ divInd b (x.2 : ℕ)) =
          (B.canonicalGuardedMediumReferenceLaw xi).probability.covariance
            (fun x ↦ divInd a
              ((B.canonicalGuardedMediumReferenceLaw xi).value x))
            (fun x ↦ divInd b
              ((B.canonicalGuardedMediumReferenceLaw xi).value x)) := by
      rfl
    exact hraw'.trans (hremainingMedium.trans htarget)
  have hmediumCorrection (q : BandPrime B.sampleData.n B.sampleData.W) :
      (B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1 =
        PaperGuardCensus.powerCorrectionCovariance
          (sigmaMixture weight nu) (fun x ↦ (x.2 : ℕ)) p.1 q.1 := by
    rw [← powerCorrectionCovariance_eq_covVV_sub_covII
      (B.canonicalGuardedMediumReferenceLaw xi) p.1 q.1]
    unfold PaperGuardCensus.powerCorrectionCovariance
    rw [hreindex p.1 q.1, hreindexI p.1 q.1]
  have hrawCorrection (q : BandPrime B.sampleData.n B.sampleData.W) :
      (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
          (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1 =
        PaperGuardCensus.powerCorrectionCovariance
          (sigmaMixture weight mu) (fun x ↦ (x.2 : ℕ)) p.1 q.1 := by
    rw [← powerCorrectionCovariance_eq_covVV_sub_covII
      (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS) p.1 q.1]
    rfl
  calc
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
          ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covVV p.1 q.1 -
            (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le hS).covII p.1 q.1)| =
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |PaperGuardCensus.powerCorrectionCovariance
            (sigmaMixture weight nu) (fun x ↦ (x.2 : ℕ)) p.1 q.1 -
          PaperGuardCensus.powerCorrectionCovariance
            (sigmaMixture weight mu) (fun x ↦ (x.2 : ℕ)) p.1 q.1| := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hmediumCorrection q, hrawCorrection q]
    _ ≤ PaperGuardCensus.guardPowerCorrectionRowError K d := by
      simpa only [S, mu, nu, Gsub, hS, score, weight] using hguard

























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
        ∀ {K d : Real},
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
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
                    K) →
                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                    @LT.lt.{0} Real Real.instLT
                      (@Erdos390.Full.FiniteProbability.guardMass.{0}
                        (@Subtype.{1} Nat fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            x)
                        (@Finset.Subtype.fintype.{0} Nat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c))
                        (@Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                          (@Subtype.{1} Nat fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              x)
                          (@Finset.Subtype.fintype.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c))
                          (@Erdos390.Full.FiniteProbability.uniformOnFinset.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            (@Finset.Nonempty.mono.{0} Nat
                              (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  Cprom Cbank G))
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  Cprom Cbank G))
                              (hremaining c)))
                          fun
                            (m :
                              @Subtype.{1} Nat fun (x : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  x) =>
                          Erdos390.Full.ValuationScoreDomination.valuationScore
                            (Erdos390.Full.ArithmeticModel.primeBand
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B)))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveNatCoefficient.{u_1, u_2} Head Band inst
                              inst_1 inst_2 inst_3 B xi)
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                              B)
                            (@Subtype.val.{1} Nat
                              (fun (x : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  x)
                              m))
                        (@Erdos390.Full.GuardedUniformCell.guardSubtype.{0} Nat instDecidableEqNat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c)
                          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            Cprom Cbank G)))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                  (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                      @LE.le.{0} Real Real.instLE
                        (@Erdos390.Full.FiniteProbability.guardPerturbation.{0}
                          (@Subtype.{1} Nat fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              x)
                          (@Finset.Subtype.fintype.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c))
                          (@Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                            (@Subtype.{1} Nat fun (x : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                x)
                            (@Finset.Subtype.fintype.{0} Nat
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c))
                            (@Erdos390.Full.FiniteProbability.uniformOnFinset.{0} Nat
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              (@Finset.Nonempty.mono.{0} Nat
                                (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    Cprom Cbank G))
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    Cprom Cbank G))
                                (hremaining c)))
                            fun
                              (m :
                                @Subtype.{1} Nat fun (x : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))
                                      c)
                                    x) =>
                            Erdos390.Full.ValuationScoreDomination.valuationScore
                              (Erdos390.Full.ArithmeticModel.primeBand
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B)))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveNatCoefficient.{u_1, u_2} Head Band
                                inst inst_1 inst_2 inst_3 B xi)
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                                B)
                              (@Subtype.val.{1} Nat
                                (fun (x : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))
                                      c)
                                    x)
                                m))
                          (@Erdos390.Full.GuardedUniformCell.guardSubtype.{0} Nat instDecidableEqNat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              Cprom Cbank G)))
                        d) →
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
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))) =>
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
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
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
                                      (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
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
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
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
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
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
                                      (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
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
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
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
                                    q)))))
                        (Erdos390.Full.PaperGuardCensus.guardPowerCorrectionRowError K d) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
