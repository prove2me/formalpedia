-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_medium_signed_profiles_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:12:31.191887+00:00
-- url     : https://prove2.me/submissions/4a68d5b9-e811-41b0-9899-3e9fe228333b

import Definitions.Def_erdos390_remaining_analytic_propositions_001
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
import Theorems.Thm_Erdos390_Full_FixedFiniteMixtureSignedSquarefree_exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos_compact
import Theorems.Thm_Erdos390_Full_GuardDeletionSquarefreeProfiles_exists_deleteGuards_squarefree_profiles
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound


section
universe u_1
theorem Erdos390.Full.FixedFiniteMixtureSignedSquarefree.exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos : Erdos390.RemainingAnalyticGoal001_003.{u_1} := @Erdos390.Full.FixedFiniteMixtureSignedSquarefree.exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos_compact
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







/-- The unmarked structured cell has a fixed positive linear density.  This
is the normalization lower bound used by all subsequent compact tilts. -/
theorem exists_structuredCell_density_lower_bound
    (P : Pattern) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ N₀ : ℕ, ∀ {n : ℕ}, N₀ ≤ n →
      paperCellDensity P A B * (n : ℝ) / 2 ≤
        ((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) := by
  obtain ⟨K, hK, Ncount, hcount⟩ :=
    exists_uniform_markedCell_paper_main_bound P hA hAB
  let c : ℝ := paperCellDensity P A B
  have hc : 0 < c := paperCellDensity_pos P hAB
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ (2 : ℝ) ≤ y n ∧ 2 * K / c ≤ L n := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
      hLTop.eventually (Filter.eventually_ge_atTop (2 * K / c))] with
      n hn hy hden
    exact ⟨hn, hy, hden⟩
  obtain ⟨Nlarge, hNlarge⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max Ncount Nlarge, ?_⟩
  intro n hN
  have hNc : Ncount ≤ n := by omega
  have hNl : Nlarge ≤ n := by omega
  obtain ⟨hn, hy, hden⟩ := hNlarge n hNl
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hL : 0 < L n := L_pos hn
  have hyNat2 : 2 ≤ yNat n := Nat.le_floor hy
  have h1d4 : 1 ≤ yNat n ^ 4 := by
    exact pow_pos (by omega : 0 < yNat n) 4
  have hbase₀ := hcount (n := n) (d := 1) hNc (by omega) h1d4
    (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hbase :
      |((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) - c * (n : ℝ)| ≤
        K * (n : ℝ) / L n := by
    simpa [c, markedCell] using hbase₀
  have hscale : 2 * K ≤ c * L n := by
    have := (div_le_iff₀ hc).1 hden
    simpa [mul_comm] using this
  have hKdiv : K / L n ≤ c / 2 := by
    apply (div_le_iff₀ hL).2
    nlinarith [hscale]
  have herr : K * (n : ℝ) / L n ≤ c * (n : ℝ) / 2 := by
    calc
      K * (n : ℝ) / L n = (K / L n) * (n : ℝ) := by ring
      _ ≤ (c / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hKdiv hnR.le
      _ = c * (n : ℝ) / 2 := by ring
  have hlower := (abs_le.mp (hbase.trans herr)).1
  dsimp only [c] at hlower ⊢
  linarith



end

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.Full.ValuationTiltCell -/
section


/-!
# Actual compact valuation tilts on a finite cell

This file substitutes the genuine valuation score into the omitted-score
comparison.  Both divisor-score moments are discharged by exact
common-multiple counting; no probabilistic independence is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.ValuationTiltCell

open ArithmeticModel DivisibilityMomentBounds FiniteProbability
open OmittedScoreCell ValuationScoreDomination

noncomputable section





/-- Uniform bound for the genuine compact valuation score using the physical
logarithm rather than the (much larger) number of prime-power columns. -/
theorem abs_valuationScore_le_log_ratio
    (P : Finset ℕ) (eta : ℕ → ℝ) {m M W : ℕ} {B L : ℝ}
    (hm : 0 < m) (hmM : m ≤ M)
    (hW : 1 < W) (hpW : ∀ p ∈ P, W ≤ p)
    (hB : 0 ≤ B) (hL : 0 < L) (heta : ∀ p ∈ P, |eta p| ≤ B) :
    |valuationScore P eta L m| ≤
      (B / L) * (Real.log (M : ℝ) / Real.log (W : ℝ)) := by
  unfold valuationScore
  calc
    |∑ p ∈ P, (eta p / L) * valuation p m| ≤
        ∑ p ∈ P, |(eta p / L) * valuation p m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ P, (|eta p| / L) * valuation p m := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul, abs_div, abs_of_pos hL,
        abs_of_nonneg (valuation_nonneg p m)]
    _ ≤ ∑ p ∈ P, (B / L) * valuation p m := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (heta p hp) hL.le)
        (valuation_nonneg p m)
    _ = (B / L) * (∑ p ∈ P, valuation p m) := by
      rw [Finset.mul_sum]
    _ ≤ (B / L) *
        (Real.log (M : ℝ) / Real.log (W : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_valuation_le_log_ratio P hm hmM hW hpW)
        (div_nonneg hB hL.le)



end

end Erdos390.Full.ValuationTiltCell

end

/- Source module: Erdos390.Full.TwoLocalRestoration -/
section


/-!
# Exact restoration of two omitted local primes

The omitted-score marked law is reweighted by the two literal local
valuation fugacities.  This file proves the exact finite identity connecting
that sequential reweighting to the full valuation tilt and then expands both
the marked numerator and the normalizer into prime-power indicators.
-/

open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel FiniteProbability ValuationScoreDomination
open LocalFugacity LocalFugacityRestoration ValuationCutoff

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Two finite probability objects are equal when their mass functions are
equal.  The remaining structure fields are propositions. -/
theorem eq_of_mass_eq (mu nu : FiniteProbability Omega)
    (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk muMass muNonneg muSum =>
      cases nu with
      | mk nuMass nuNonneg nuSum =>
          simp only [FiniteProbability.mk.injEq]
          exact h





end FiniteProbability

namespace TwoLocalRestoration









section Cell

variable {S : Finset ℕ}





end Cell

end TwoLocalRestoration

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

/- Source module: Erdos390.Full.PaperGuardedStructuredSample -/
section


/-!
# Canonical guarded structured sample

This module attaches the concrete guard ledger to the literal physical
structured cells used by the bridge.  Both physical endpoints are definitionally
`floor(A*n)`, and nonemptiness after guard deletion is derived from the proved
Dickman cell-density theorem and the concrete `O(y log n)` image census.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open PaperScaleMarkedCell
open PaperBridgeFit

noncomputable section



variable {Head : Type*} [Fintype Head]





/-- Every raw cell has its proved positive Dickman density eventually. -/
theorem eventually_rawCell_density
    (P : Head → Pattern) (I : PhysicalIntervals) :
    ∀ᶠ n : ℕ in atTop, ∀ c : Cell Head,
      paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) *
          (n : ℝ) / 2 ≤ (rawCell P I n c).card := by
  rw [Filter.eventually_all]
  intro c
  obtain ⟨N₀, hN₀⟩ := exists_structuredCell_density_lower_bound
    (P c.1) (I.lower_pos c.2) (I.lower_lt_upper c.2)
  filter_upwards [eventually_ge_atTop N₀] with n hn
  simpa only [rawCell] using hN₀ hn























end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperPrimePowerChamberError -/
section


/-!
# Explicit chamber-error majorants for prime-power aggregation

This file replaces the nested restoration ledger by one scalar remainder at
the natural product-reciprocal scale.  The scalar is explicit, uniform over
all moving primes and exponents, and retains the vanishing omitted-score and
`1 / log n` factors needed before the harmonic prime sum is taken.
-/

namespace Erdos390.Full.PaperPrimePowerChamberError

open ArithmeticModel Scale HeadPattern
open OmittedTiltPairChamber FullTiltPairChamber
open LocalFugacityBounds TwoLocalRestorationBound
open PaperTwoLocalRestorationBound PaperScaleMarkedCell
open FullTiltPrimePowerCovariance

noncomputable section







theorem singleWeight_nonneg (p r : ℕ) : 0 ≤ singleWeight p r := by
  unfold singleWeight
  positivity



theorem pairWeight_nonneg (p q r s : ℕ) :
    0 ≤ pairWeight p q r s := by
  unfold pairWeight
  positivity





























end

end Erdos390.Full.PaperPrimePowerChamberError

end

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



theorem guardSquarefreeError_nonneg
    (S G : Finset ℕ) (scoreBound : ℝ) (n : ℕ) :
    0 ≤ guardSquarefreeError S G scoreBound n := by
  unfold guardSquarefreeError
  positivity



/-- Reindex the preceding result to the literal subtype of the difference
finset used by the bridge sample. -/
theorem remaining_tilt_squarefree_profiles
    (S G : Finset ℕ) (hS : S.Nonempty) (hR : (S \ G).Nonempty)
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
    let remaining := (uniformOnFinset (S \ G) hR).exponentialTilt
      (fun z ↦ score (remainingEmbedding S G z))
    (∀ p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |remaining.expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q 1 1)| ≤
          (E + guardSquarefreeError S G K n) * pairWeight p q 1 1) ∧
    (∀ p, p ∈ primeBand n W →
      |remaining.expect (fun m ↦ divInd p (m : ℕ)) -
        paperDivisibilityMain n p| ≤
          (E + guardSquarefreeError S G K n) * singleWeight p 1) := by
  dsimp only
  obtain ⟨hsmall, hpairDeleted, hsingleDeleted⟩ :=
    exists_deleteGuards_squarefree_profiles S G hS score K hscore
      hsmallCensus hpair hsingle
  constructor
  · intro p hp q hq
    have hreindex := deleteGuards_tilted_uniform_expect_remaining_eq
      S G hS hR score hsmall
      (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ))
    have hdel := hpairDeleted p hp q hq
    rw [hreindex] at hdel
    simpa only [remainingEmbedding_value] using hdel
  · intro p hp
    have hreindex := deleteGuards_tilted_uniform_expect_remaining_eq
      S G hS hR score hsmall (fun m ↦ divInd p (m : ℕ))
    have hdel := hsingleDeleted p hp
    rw [hreindex] at hdel
    simpa only [remainingEmbedding_value] using hdel

end

end Erdos390.Full.GuardDeletionSquarefreeProfiles

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

/- Source module: Erdos390.Full.GuardSquarefreeErrorRate -/
section


/-!
# Vanishing rate of the squarefree guard error

The reciprocal guard conversion costs `y²`.  Since the concrete ledger has
`O(y log n)` guards and each raw cell has positive linear density, the final
cost is `O((log n)/n^(1/3))`; it still vanishes after multiplication by
`log log n`.  This file proves that rate with the literal scales.
-/

open Filter Topology

namespace Erdos390.Full.GuardSquarefreeErrorRate

open ArithmeticModel Scale PaperGuardCensus
open GuardDeletionSquarefreeProfiles

noncomputable section

private theorem tendsto_inv_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (0 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (0 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, Real.rpow_zero]

private theorem tendsto_L_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (1 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, L, Real.rpow_one]

private theorem tendsto_L_sq_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n ^ 2 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (2 : ℝ) / (n : ℝ) ^ a)
      atTop (nhds 0) at hnat
  simpa [L, Real.rpow_natCast] using hnat

private theorem y_cube_div_nat_eq_inv_rpow {n : ℕ} (hn : 0 < n) :
    y n ^ 3 / (n : ℝ) = 1 / (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 *
          (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) := by
    calc
      ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 *
          (n : ℝ) ^ (1 / 3 : ℝ) =
        (((n : ℝ) ^ (2 / 9 : ℝ) *
            (n : ℝ) ^ (2 / 9 : ℝ)) *
          ((n : ℝ) ^ (2 / 9 : ℝ) *
            (n : ℝ) ^ (1 / 3 : ℝ))) := by ring
      _ = (n : ℝ) ^ ((2 / 9 : ℝ) + 2 / 9) *
          (n : ℝ) ^ ((2 / 9 : ℝ) + 1 / 3) := by
        rw [Real.rpow_add hnR, Real.rpow_add hnR]
      _ = (n : ℝ) ^ (((2 / 9 : ℝ) + 2 / 9) +
          ((2 / 9 : ℝ) + 1 / 3)) := by
        rw [← Real.rpow_add hnR]
      _ = (n : ℝ) := by norm_num [Real.rpow_one]
  unfold y
  field_simp [(Real.rpow_pos_of_pos hnR (1 / 3 : ℝ)).ne', hnR.ne']
  nlinarith

private theorem census_mul_y_sq_expansion
    (Cprom Cbank n : ℕ) (hn : 0 < n) :
    censusRatioMajorant Cprom Cbank n * y n ^ 2 =
      (Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
        3 * (Cbank : ℝ) *
          (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
            2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ))) := by
  rw [censusRatioMajorant]
  rw [show
    (((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n /
        (n : ℝ)) * y n ^ 2 =
      ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
        (y n ^ 3 / (n : ℝ)) by ring]
  rw [y_cube_div_nat_eq_inv_rpow hn]
  ring

/-- The concrete census still vanishes after the reciprocal `y²` conversion. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_zero (Cprom Cbank : ℕ) :
    Tendsto (fun n : ℕ ↦ censusRatioMajorant Cprom Cbank n * y n ^ 2)
      atTop (nhds 0) := by
  let a : ℝ := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hzero := tendsto_inv_nat_rpow_zero a ha
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hsum : Tendsto
      (fun n : ℕ ↦
        (Cprom : ℝ) * (1 / (n : ℝ) ^ a) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ a + 2 * (1 / (n : ℝ) ^ a)))
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hzero.const_mul (Cprom : ℝ)).add
        ((hlog.add (hzero.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa only [a] using (census_mul_y_sq_expansion Cprom Cbank n hn).symm

/-- The unweighted census ratio itself tends to zero.  This follows from
the stronger `y²`-weighted estimate because `1 ≤ y²` eventually. -/
theorem tendsto_censusRatioMajorant_zero (Cprom Cbank : ℕ) :
    Tendsto (censusRatioMajorant Cprom Cbank) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_censusRatioMajorant_mul_y_sq_zero Cprom Cbank)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    unfold censusRatioMajorant
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    have hcoef : 0 ≤
        (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hyOne : (1 : ℝ) ≤ y n := by
      unfold y
      exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
    have hySq : (1 : ℝ) ≤ y n ^ 2 := by nlinarith
    have hcensus0 : 0 ≤ censusRatioMajorant Cprom Cbank n := by
      unfold censusRatioMajorant
      have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
      have hcoef : 0 ≤
          (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
      exact div_nonneg
        (mul_nonneg hcoef (Scale.y_pos hn).le) (by positivity)
    calc
      censusRatioMajorant Cprom Cbank n =
          censusRatioMajorant Cprom Cbank n * 1 := by ring
      _ ≤ censusRatioMajorant Cprom Cbank n * y n ^ 2 :=
        mul_le_mul_of_nonneg_left hySq hcensus0

/-- The same error survives the extra moving-low harmonic loss
`log (L n)`. -/
theorem tendsto_censusRatioMajorant_mul_y_sq_mul_logL_zero
    (Cprom Cbank : ℕ) :
    Tendsto (fun n : ℕ ↦
      censusRatioMajorant Cprom Cbank n * y n ^ 2 * Real.log (L n))
      atTop (nhds 0) := by
  let a : ℝ := 1 / 3
  have ha : 0 < a := by norm_num [a]
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hlogSq := tendsto_L_sq_div_nat_rpow_zero a ha
  let upper : ℕ → ℝ := fun n ↦
    (Cprom : ℝ) * (L n / (n : ℝ) ^ a) +
      3 * (Cbank : ℝ) *
        (L n ^ 2 / (n : ℝ) ^ a +
          2 * (L n / (n : ℝ) ^ a))
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp only [upper]
    simpa only [mul_zero, add_zero] using
      (hlog.const_mul (Cprom : ℝ)).add
        ((hlogSq.add (hlog.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ L n :=
    hLTop.eventually (eventually_ge_atTop 1)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop 0, hLge] with n hn hLn
    rw [census_mul_y_sq_expansion Cprom Cbank n hn]
    exact mul_nonneg (by positivity) (Real.log_nonneg hLn)
  · filter_upwards [eventually_gt_atTop 0, hLge] with n hn hLn
    have hlogL : Real.log (L n) ≤ L n :=
      (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hLn)).trans (by linarith)
    rw [census_mul_y_sq_expansion Cprom Cbank n hn]
    dsimp only [upper, a]
    have hbase0 : 0 ≤
        (Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
              2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ))) := by
      positivity
    calc
      ((Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
            3 * (Cbank : ℝ) *
              (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
                2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)))) * Real.log (L n) ≤
          ((Cprom : ℝ) * (1 / (n : ℝ) ^ (1 / 3 : ℝ)) +
            3 * (Cbank : ℝ) *
              (L n / (n : ℝ) ^ (1 / 3 : ℝ) +
                2 * (1 / (n : ℝ) ^ (1 / 3 : ℝ)))) * L n :=
        mul_le_mul_of_nonneg_left hlogL hbase0
      _ = (Cprom : ℝ) * (L n / (n : ℝ) ^ (1 / 3 : ℝ)) +
          3 * (Cbank : ℝ) *
            (L n ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ) +
              2 * (L n / (n : ℝ) ^ (1 / 3 : ℝ))) := by ring

/-- Multiplication by fixed cell/box constants preserves both vanishing
statements. -/
theorem tendsto_guardRateMajorant_zero
    (Cprom Cbank : ℕ) (constant : ℝ) :
    Tendsto (fun n : ℕ ↦ constant *
      (censusRatioMajorant Cprom Cbank n * y n ^ 2))
      atTop (nhds 0) := by
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_censusRatioMajorant_mul_y_sq_zero Cprom Cbank))

theorem tendsto_guardRateMajorant_mul_logL_zero
    (Cprom Cbank : ℕ) (constant : ℝ) :
    Tendsto (fun n : ℕ ↦ constant *
      (censusRatioMajorant Cprom Cbank n * y n ^ 2) * Real.log (L n))
      atTop (nhds 0) := by
  have hc : Tendsto (fun _n : ℕ ↦ constant) atTop (nhds constant) :=
    tendsto_const_nhds
  have h := hc.mul
    (tendsto_censusRatioMajorant_mul_y_sq_mul_logL_zero Cprom Cbank)
  simpa only [mul_zero, mul_assoc] using h

/-- The literal squarefree deletion error of a concrete raw cell is bounded
by the preceding universal vanishing rate. -/
theorem guardSquarefreeError_rawCell_le_rateMajorant
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {n Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (c : PaperBridgeFit.Cell Head) (hn : 1 ≤ n)
    (hdensity :
      PaperScaleMarkedCell.paperCellDensity (P c.1)
          (I.lower c.2) (I.upper c.2) * (n : ℝ) / 2 ≤
        (rawCell P I n c).card)
    (K : ℝ) :
    guardSquarefreeError (rawCell P I n c) G.guards K n ≤
      (4 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
        (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by
  let density := PaperScaleMarkedCell.paperCellDensity (P c.1)
    (I.lower c.2) (I.upper c.2)
  have hdensityPos : 0 < density :=
    PaperScaleMarkedCell.paperCellDensity_pos (P c.1) (I.lower_lt_upper c.2)
  have hratio := guard_card_div_rawCell_le P I G c hn hdensity
  have hratio0 : 0 ≤ (G.guards.card : ℝ) /
      ((rawCell P I n c).card : ℝ) := by positivity
  have hcensus0 : 0 ≤ censusRatioMajorant Cprom Cbank n := by
    unfold censusRatioMajorant
    have hL : 0 ≤ L n := Real.log_nonneg (by exact_mod_cast hn)
    have hnR : 0 ≤ (n : ℝ) := by positivity
    have hcoef : 0 ≤
        (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by positivity
    exact div_nonneg (mul_nonneg hcoef (Scale.y_pos (by omega : 0 < n)).le) hnR
  have hmajor0 : 0 ≤
      2 * censusRatioMajorant Cprom Cbank n / density :=
    div_nonneg (mul_nonneg (by norm_num) hcensus0) hdensityPos.le
  have hyNat : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (by omega : 0 < n)).le
  have hyNat0 : 0 ≤ (yNat n : ℝ) := by positivity
  have hy0 : 0 ≤ y n := (Scale.y_pos (by omega : 0 < n)).le
  have hySq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyNat0 hy0).2 hyNat
  unfold guardSquarefreeError
  rw [show 2 * (Real.exp (2 * K) * (G.guards.card : ℝ) /
        ((rawCell P I n c).card : ℝ)) * (yNat n : ℝ) ^ 2 =
      2 * Real.exp (2 * K) *
        ((G.guards.card : ℝ) / ((rawCell P I n c).card : ℝ)) *
          (yNat n : ℝ) ^ 2 by ring]
  calc
    2 * Real.exp (2 * K) *
          ((G.guards.card : ℝ) / ((rawCell P I n c).card : ℝ)) *
          (yNat n : ℝ) ^ 2 ≤
        2 * Real.exp (2 * K) *
          (2 * censusRatioMajorant Cprom Cbank n / density) *
          (yNat n : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio
          (mul_nonneg (by norm_num) (Real.exp_pos _).le))
        (sq_nonneg _)
    _ ≤ 2 * Real.exp (2 * K) *
          (2 * censusRatioMajorant Cprom Cbank n / density) * y n ^ 2 :=
      mul_le_mul_of_nonneg_left hySq
        (mul_nonneg
          (mul_nonneg (by norm_num) (Real.exp_pos _).le) hmajor0)
    _ = (4 * Real.exp (2 * K) / density) *
          (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by ring
    _ = _ := by rfl

/-- For a fixed score box, the concrete ledger has exponentially tilted
mass at most one half in every raw head/physical cell eventually. -/
theorem eventually_exp_two_mul_guardRatio_rawCell_le_half
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      Real.exp (2 * K) * ((G n).guards.card : ℝ) /
        ((rawCell P I n c).card : ℝ) ≤ (1 : ℝ) / 2 := by
  have hdensity := eventually_rawCell_density P I
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      (2 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
        censusRatioMajorant Cprom Cbank n ≤ (1 : ℝ) / 2 := by
    rw [Filter.eventually_all]
    intro c
    let constant := 2 * Real.exp (2 * K) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hconst : Tendsto (fun _n : ℕ ↦ constant) atTop (nhds constant) :=
      tendsto_const_nhds
    have ht := hconst.mul
      (tendsto_censusRatioMajorant_zero Cprom Cbank)
    have ht0 : Tendsto (fun n : ℕ ↦
        (2 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
          censusRatioMajorant Cprom Cbank n) atTop (nhds 0) := by
      simpa only [constant, mul_zero] using ht
    exact ht0.eventually (eventually_le_nhds (by norm_num))
  filter_upwards [hdensity, hsmall, eventually_gt_atTop 0] with
      n hdens hsmalln hn c
  have hratio := guard_card_div_rawCell_le P I (G n) c
    (by omega : 1 ≤ n) (hdens c)
  have hexp0 : 0 ≤ Real.exp (2 * K) := (Real.exp_pos _).le
  calc
    Real.exp (2 * K) * ((G n).guards.card : ℝ) /
        ((rawCell P I n c).card : ℝ) =
      Real.exp (2 * K) *
        (((G n).guards.card : ℝ) / ((rawCell P I n c).card : ℝ)) := by ring
    _ ≤ Real.exp (2 * K) *
        (2 * censusRatioMajorant Cprom Cbank n /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) :=
      mul_le_mul_of_nonneg_left hratio hexp0
    _ = (2 * Real.exp (2 * K) /
          PaperScaleMarkedCell.paperCellDensity (P c.1)
            (I.lower c.2) (I.upper c.2)) *
        censusRatioMajorant Cprom Cbank n := by ring
    _ ≤ (1 : ℝ) / 2 := hsmalln c







theorem canonicalGuardSquarefreeError_nonneg
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank)
    (K : ℝ) (n : ℕ) :
    0 ≤ canonicalGuardSquarefreeError P I G K n := by
  unfold canonicalGuardSquarefreeError
  exact Finset.sum_nonneg fun c hc ↦
    guardSquarefreeError_nonneg _ _ _ _

/-- The family-aggregated reciprocal guard error tends to zero. -/
theorem tendsto_canonicalGuardSquarefreeError_zero
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank) (K : ℝ) :
    Tendsto (canonicalGuardSquarefreeError P I G K) atTop (nhds 0) := by
  have hcell (c : PaperBridgeFit.Cell Head) : Tendsto
      (fun n : ℕ ↦ guardSquarefreeError
        (rawCell P I n c) (G n).guards K n) atTop (nhds 0) := by
    let constant := 4 * Real.exp (2 * K) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hupper := tendsto_guardRateMajorant_zero Cprom Cbank constant
    have hdensity := eventually_rawCell_density P I
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards with n
      exact guardSquarefreeError_nonneg _ _ _ _
    · filter_upwards [hdensity, eventually_gt_atTop 0] with n hdens hn
      simpa only [constant] using
        guardSquarefreeError_rawCell_le_rateMajorant
          P I (G n) c (by omega : 1 ≤ n) (hdens c) K
  have hsum := tendsto_finset_sum
    (Finset.univ : Finset (PaperBridgeFit.Cell Head))
    (fun c hc ↦ hcell c)
  simpa only [canonicalGuardSquarefreeError,
    Finset.sum_const_zero] using hsum

/-- The same family error remains negligible after the moving-low harmonic
loss. -/
theorem tendsto_canonicalGuardSquarefreeError_mul_logL_zero
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank) (K : ℝ) :
    Tendsto (fun n : ℕ ↦
      canonicalGuardSquarefreeError P I G K n * Real.log (L n))
      atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) :=
    (hLTop.eventually (eventually_ge_atTop 1)).mono fun n hn ↦
      Real.log_nonneg hn
  have hcell (c : PaperBridgeFit.Cell Head) : Tendsto
      (fun n : ℕ ↦ guardSquarefreeError
          (rawCell P I n c) (G n).guards K n * Real.log (L n))
        atTop (nhds 0) := by
    let constant := 4 * Real.exp (2 * K) /
      PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2)
    have hupper :=
      tendsto_guardRateMajorant_mul_logL_zero Cprom Cbank constant
    have hdensity := eventually_rawCell_density P I
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [hlog0] with n hlog
      exact mul_nonneg (guardSquarefreeError_nonneg _ _ _ _) hlog
    · filter_upwards [hdensity, eventually_gt_atTop 0, hlog0]
        with n hdens hn hlog
      have hn1 : 1 ≤ n := by omega
      have hguard := guardSquarefreeError_rawCell_le_rateMajorant
        (Head := Head) P I (G n) c hn1 (hdens c) K
      have hguard' : guardSquarefreeError
          (rawCell P I n c) (G n).guards K n ≤
        constant * (censusRatioMajorant Cprom Cbank n * y n ^ 2) := by
        simpa only [constant] using hguard
      exact mul_le_mul_of_nonneg_right hguard' hlog
  have hsum := tendsto_finset_sum
    (Finset.univ : Finset (PaperBridgeFit.Cell Head))
    (fun c hc ↦ hcell c)
  have hsum0 : Tendsto (fun n : ℕ ↦
      ∑ c : PaperBridgeFit.Cell Head,
        guardSquarefreeError (rawCell P I n c) (G n).guards K n *
          Real.log (L n)) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using hsum
  apply hsum0.congr'
  filter_upwards with n
  unfold canonicalGuardSquarefreeError
  rw [Finset.sum_mul]

end

end Erdos390.Full.GuardSquarefreeErrorRate

end

/- Source module: Erdos390.Full.FixedFiniteMixtureSignedSquarefree -/
section


/-!
# Signed squarefree profiles for a fixed finite family of cells

The prime-power conclusion of paper Lemma 7.5 is an absolute tail estimate.
The arithmetic inverse in Lemma 8.4 instead needs the signed one- and
two-divisor profiles before covariance is formed.  The proof of the former
already constructs a common finite-family profile with one harmonic loss to
spare.  This file exports that stronger intermediate conclusion explicitly,
without taking it as a hypothesis.
-/

open Filter Topology

namespace Erdos390.Full.FixedFiniteMixtureSignedSquarefree

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPairHarmonicRate
open PaperTwoLocalRestorationBound LocalFugacityBounds
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerRemainderRate PaperScaleMarkedCell
open PaperValuationCutoff PaperPrimePowerAuxiliaryPrime
open FixedFiniteMixtureFullUniform

noncomputable section

variable {Cell : Type*} [Fintype Cell]



/-- Backwards-compatible paper normalization of the positive-endpoint
core. -/
theorem exists_boxIndependent_fixedFiniteMixture_signed_profiles
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 1 ≤ C c) (hC_le : ∀ c, C c ≤ Cmax) :
    ∀ W : ℕ, 1 < W →
      (∀ c, ∀ p ∈ (H c).primes, p ≤ W) →
    ∀ B : ℝ, 0 ≤ B →
      ∃ signedError : ℕ → ℝ,
        (∀ n, 0 ≤ signedError n) ∧
        Tendsto signedError atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ signedError n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := fun c ↦ structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          (∀ c, (S c).Nonempty) ∧
            ∀ hS : ∀ c, (S c).Nonempty,
            let law := fun c ↦ widen
              (valuationTilt (H c) (physicalBound (A c) n)
                (physicalBound (C c) n) (yNat n) (hS c)
                (primeBand n W) eta (L n))
              (physicalBound_mono (hC_le c) n)
            (∀ c p, p ∈ primeBand n W →
              ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
              pairPower p q r s ≤ yNat n ^ 4 →
              |(law c).probability.expect
                  (fun omega ↦ divInd (pairPower p q r s)
                    ((law c).value omega)) -
                paperDivisibilityMain n (pairPower p q r s)| ≤
                  signedError n * pairWeight p q r s) ∧
            (∀ c p, p ∈ primeBand n W →
              |(law c).probability.expect
                  (fun omega ↦ divInd p ((law c).value omega)) -
                paperDivisibilityMain n p| ≤
                  signedError n * singleWeight p 1) := by
  exact exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos
    H A C Cmax hA hAC
      (fun c ↦ lt_of_lt_of_le zero_lt_one (hC c)) hC_le

end

end Erdos390.Full.FixedFiniteMixtureSignedSquarefree

end

/- Source module: Erdos390.Full.PaperActualSquarefreeReference -/
section


/-!
# The actual bridge squarefree law and the canonical reference operator

This file closes two finite-probability identifications needed in Lemma 8.4.
First, a reciprocal signed profile for the medium-only law survives the
literal physical/head component tilt at the same reciprocal scale.  Second,
the partition-function-reweighted mixture of those component laws is exactly
the `BridgeData.tiltedLaw`, including the between-cell covariance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber PaperPrimePowerChamberError
open StructuredCells ValuationScoreDomination

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







/-- Replacing a finite set by an equal finite set does not change a uniform
valuation tilt or any divisor expectation.  This small transport lemma keeps
dependent nonemptiness proofs out of the marked-profile argument. -/
theorem uniformValuationTilt_expect_divInd_eq_of_finset_eq
    (S T : Finset ℕ) (hST : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (primes : Finset ℕ) (eta : ℕ → ℝ) (logScale : ℝ) (D : ℕ) :
    ((uniformOnFinset S hS).exponentialTilt
        (fun m ↦ valuationScore primes eta logScale (m : ℕ))).expect
        (fun m ↦ divInd D (m : ℕ)) =
      ((uniformOnFinset T hT).exponentialTilt
        (fun m ↦ valuationScore primes eta logScale (m : ℕ))).expect
        (fun m ↦ divInd D (m : ℕ)) := by
  subst T
  have hp : hT = hS := Subsingleton.elim _ _
  subst hT
  rfl

/-- A compact effective-prime box gives a pointwise score bound on the
*unguarded* cell with a constant independent of the cell and of `n`. -/
theorem abs_unguardedCell_mediumScore_le [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) {C A : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hA : 0 ≤ A)
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A)
    (m : structuredCell (B.sampleData.pattern c.1)
      (B.sampleData.lo c.2) (B.sampleData.hi c.2)
      (yNat B.sampleData.n)) :
    |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
      A * PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W := by
  have hmpos : 0 < (m : ℕ) :=
    pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hmhi : (m : ℕ) ≤ B.sampleData.hi c.2 :=
    (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have hmC : (m : ℕ) ≤ physicalBound C B.sampleData.n :=
    hmhi.trans (hhi c.2)
  have hpW : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      B.sampleData.W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand hp).le
  have hetaNat : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi p| ≤ A := by
    intro p hp
    rw [B.effectiveNatCoefficient_of_mem xi hp]
    exact heta ⟨p, hp⟩
  have hraw := ValuationTiltCell.abs_valuationScore_le_log_ratio
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) hmpos hmC hW hpW hA B.L_pos hetaNat
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hcoef : 0 ≤ A / B.L := div_nonneg hA B.L_pos.le
  calc
    |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
      (A / B.L) *
        (Real.log (physicalBound C B.sampleData.n : ℝ) /
          Real.log (B.sampleData.W : ℝ)) := hraw
    _ ≤ (A / B.L) *
        ((PaperStatisticNorm.physicalLogCoefficient C * B.L) /
          Real.log (B.sampleData.W : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (PaperStatisticNorm.BridgeData.log_physicalBound_le B hC)
          hlogW.le) hcoef
    _ = A * PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W := by
      unfold PaperStatisticNorm.valuationLogCoefficient
      field_simp [B.L_pos.ne', hlogW.ne']



/-- The literal medium-only bridge law is the conditional guard deletion of
the corresponding unguarded structured-cell tilt.  Consequently signed
profiles on the unguarded cell transfer to `cellMediumLaw` with the explicit
reciprocal guard cost. -/
theorem cellMediumLaw_squarefree_profiles_of_unguarded [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) {K E : ℝ}
    (hS : (structuredCell (B.sampleData.pattern c.1)
      (B.sampleData.lo c.2) (B.sampleData.hi c.2)
      (yNat B.sampleData.n)).Nonempty)
    (hscore : ∀ m : structuredCell (B.sampleData.pattern c.1)
        (B.sampleData.lo c.2) (B.sampleData.hi c.2)
        (yNat B.sampleData.n),
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ K)
    (hsmallCensus :
      Real.exp (2 * K) * (B.sampleData.guards.card : ℝ) /
        ((structuredCell (B.sampleData.pattern c.1)
          (B.sampleData.lo c.2) (B.sampleData.hi c.2)
          (yNat B.sampleData.n)).card : ℝ) ≤ (1 : ℝ) / 2)
    (hpair : ∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |((uniformOnFinset
          (structuredCell (B.sampleData.pattern c.1)
            (B.sampleData.lo c.2) (B.sampleData.hi c.2)
            (yNat B.sampleData.n))
          hS).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤ E * pairWeight p q 1 1)
    (hsingle : ∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |((uniformOnFinset
          (structuredCell (B.sampleData.pattern c.1)
            (B.sampleData.lo c.2) (B.sampleData.hi c.2)
            (yNat B.sampleData.n))
          hS).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
          (fun m ↦ divInd p (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          E * singleWeight p 1) :
    (∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.cellMediumLaw xi c).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        (E + GuardDeletionSquarefreeProfiles.guardSquarefreeError
          (structuredCell (B.sampleData.pattern c.1)
            (B.sampleData.lo c.2) (B.sampleData.hi c.2)
            (yNat B.sampleData.n)) B.sampleData.guards K B.sampleData.n) *
          pairWeight p q 1 1) ∧
    (∀ p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.cellMediumLaw xi c).expect (fun m ↦ divInd p (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        (E + GuardDeletionSquarefreeProfiles.guardSquarefreeError
          (structuredCell (B.sampleData.pattern c.1)
            (B.sampleData.lo c.2) (B.sampleData.hi c.2)
            (yNat B.sampleData.n)) B.sampleData.guards K B.sampleData.n) *
          singleWeight p 1) := by
  let S := structuredCell (B.sampleData.pattern c.1)
    (B.sampleData.lo c.2) (B.sampleData.hi c.2) (yNat B.sampleData.n)
  have hR : (S \ B.sampleData.guards).Nonempty := by
    simpa only [S, StructuredSampleData.cellFinset] using
      B.sampleData.cell_nonempty c
  have hS' : S.Nonempty := by simpa only [S] using hS
  let score : S → ℝ := fun m ↦
    valuationScore (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L (m : ℕ)
  have hprofiles :=
    GuardDeletionSquarefreeProfiles.remaining_tilt_squarefree_profiles
      S B.sampleData.guards hS' hR score K
      (by simpa only [score, S] using hscore)
      hsmallCensus (by simpa only [S, score] using hpair)
      (by simpa only [S, score] using hsingle)
  have hmedium : B.cellMediumLaw xi c =
      (uniformOnFinset (S \ B.sampleData.guards) hR).exponentialTilt
        (fun z ↦ score
          (GuardedUniformCell.remainingEmbedding S B.sampleData.guards z)) := by
    unfold cellMediumLaw guardedCellProbability
    let hR₀ : (S \ B.sampleData.guards).Nonempty := by
      simpa only [S, StructuredSampleData.cellFinset] using
        B.sampleData.cell_nonempty c
    change
      (uniformOnFinset (S \ B.sampleData.guards) hR₀).exponentialTilt
          (sigmaCellScore (B.scaledMediumScore xi) c) =
        (uniformOnFinset (S \ B.sampleData.guards) hR).exponentialTilt
          (fun z ↦ score
            (GuardedUniformCell.remainingEmbedding S B.sampleData.guards z))
    have hbase : uniformOnFinset (S \ B.sampleData.guards) hR₀ =
        uniformOnFinset (S \ B.sampleData.guards) hR := by
      apply FiniteProbability.eq_of_mass_eq
      rfl
    rw [hbase]
    apply congrArg ((uniformOnFinset (S \ B.sampleData.guards) hR).exponentialTilt)
    funext z
    exact B.sigmaCellScore_scaledMedium_eq_valuationScore xi c z |>.trans rfl
  rw [hmedium]
  simpa only [S, score] using hprofiles

/-- Uniform signed profiles for the actual medium-tilted guarded bridge
cells.  The profile is derived from the fixed finite marked-cell theorem and
the concrete ledger census.  Its error, including guard deletion, still
vanishes after multiplication by `log (L n)`.

Only structural identifications of `sampleData` with the canonical physical
cells occur as hypotheses; no probability, covariance, operator, or inverse
estimate is assumed. -/
theorem exists_boxIndependent_actual_medium_signed_profiles
    [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hupperOne : ∀ sigma, 1 ≤ I.upper sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∀ W : ℕ, 1 < W →
      (∀ h, ∀ p ∈ (Phead h).primes, p ≤ W) →
    ∀ Acoef : ℝ, 0 ≤ Acoef →
    ∃ profileError : ℕ → ℝ,
      (∀ n, 0 ≤ profileError n) ∧
      Filter.Tendsto profileError Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n : ℕ ↦ profileError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n →
          B.sampleData.pattern = Phead →
          (∀ sigma, B.sampleData.lo sigma =
            physicalBound (I.lower sigma) B.sampleData.n) →
          (∀ sigma, B.sampleData.hi sigma =
            physicalBound (I.upper sigma) B.sampleData.n) →
          B.sampleData.guards = (ledger B.sampleData.n).guards →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          B.sampleData.W = W →
          (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
            ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
            |(B.cellMediumLaw xi c).expect
                (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
              PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
                (pairPower p q 1 1)| ≤
              profileError B.sampleData.n * pairWeight p q 1 1) ∧
          (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
            |(B.cellMediumLaw xi c).expect
                (fun m ↦ divInd p (m : ℕ)) -
              PaperScaleMarkedCell.paperDivisibilityMain
                B.sampleData.n p| ≤
              profileError B.sampleData.n * singleWeight p 1) := by
  intro W hW hsupport Acoef hAcoef
  let H : Cell Head → HeadPattern.Pattern := fun c ↦ Phead c.1
  let Alower : Cell Head → ℝ := fun c ↦ I.lower c.2
  let Cupper : Cell Head → ℝ := fun c ↦ I.upper c.2
  obtain ⟨rawError, hraw0, hrawT, hrawRate, Nraw, hraw⟩ :=
    FixedFiniteMixtureSignedSquarefree.exists_boxIndependent_fixedFiniteMixture_signed_profiles
      H Alower Cupper Cmax
      (fun c ↦ I.lower_pos c.2) (fun c ↦ I.lower_lt_upper c.2)
      (fun c ↦ hupperOne c.2) (fun c ↦ hupperMax c.2)
      W hW (fun c ↦ hsupport c.1) Acoef hAcoef
  let K := Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W
  let guardError : ℕ → ℝ :=
    Erdos390.Full.GuardSquarefreeErrorRate.canonicalGuardSquarefreeError
      Phead I ledger K
  let profileError : ℕ → ℝ := fun n ↦ rawError n + guardError n
  have hCmax : 1 ≤ Cmax := (hupperOne .minus).trans (hupperMax .minus)
  have hguard0 (n : ℕ) : 0 ≤ guardError n := by
    exact Erdos390.Full.GuardSquarefreeErrorRate.canonicalGuardSquarefreeError_nonneg
      Phead I ledger K n
  have hguardT : Filter.Tendsto guardError Filter.atTop (nhds 0) := by
    exact Erdos390.Full.GuardSquarefreeErrorRate.tendsto_canonicalGuardSquarefreeError_zero
      Phead I ledger K
  have hguardRate : Filter.Tendsto
      (fun n : ℕ ↦ guardError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    exact Erdos390.Full.GuardSquarefreeErrorRate.tendsto_canonicalGuardSquarefreeError_mul_logL_zero
      Phead I ledger K
  have hprofile0 (n : ℕ) : 0 ≤ profileError n := by
    exact add_nonneg (hraw0 n) (hguard0 n)
  have hprofileT : Filter.Tendsto profileError Filter.atTop (nhds 0) := by
    simpa only [profileError, add_zero] using hrawT.add hguardT
  have hprofileRate : Filter.Tendsto
      (fun n : ℕ ↦ profileError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    simpa only [profileError, add_mul, add_zero] using
      hrawRate.add hguardRate
  have hsmallEvent :=
    Erdos390.Full.GuardSquarefreeErrorRate.eventually_exp_two_mul_guardRatio_rawCell_le_half
      Phead I Cprom Cbank ledger K
  obtain ⟨Nguard, hNguard⟩ := (Filter.eventually_atTop.1 hsmallEvent)
  let N₀ := max Nraw Nguard
  refine ⟨profileError, hprofile0, hprofileT, hprofileRate, N₀, ?_⟩
  intro Band _instBand _instBandDec B xi hN hpattern hlo hhi hguards heta hBW
  have hNraw : Nraw ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans hN
  have hNguard' : Nguard ≤ B.sampleData.n :=
    (Nat.le_max_right _ _).trans hN
  have hetaNat : ∀ z ∈ primeBand B.sampleData.n W,
      |B.effectiveNatCoefficient xi z| ≤ Acoef := by
    intro z hz
    have hzB : z ∈ primeBand B.sampleData.n B.sampleData.W := by
      simpa only [hBW] using hz
    rw [B.effectiveNatCoefficient_of_mem xi hzB]
    exact heta ⟨z, hzB⟩
  obtain ⟨hSraw, hrawProfiles⟩ :=
    hraw (B.effectiveNatCoefficient xi) hNraw hetaNat
  have hrawProfiles' := hrawProfiles hSraw
  have hsmallAll := hNguard B.sampleData.n hNguard'
  have hhiC : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound Cmax B.sampleData.n := by
    intro sigma
    rw [hhi sigma]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax sigma) B.sampleData.n
  let Sfixed : Cell Head → Finset ℕ := fun c ↦
    PaperGuardCensus.rawCell Phead I B.sampleData.n c
  let Sbridge : Cell Head → Finset ℕ := fun c ↦
    structuredCell (B.sampleData.pattern c.1)
      (B.sampleData.lo c.2) (B.sampleData.hi c.2) (yNat B.sampleData.n)
  have hSfixed (c : Cell Head) : (Sfixed c).Nonempty := by
    simpa only [Sfixed, PaperGuardCensus.rawCell, H, Alower, Cupper] using
      hSraw c
  have hSbridge (c : Cell Head) : (Sbridge c).Nonempty := by
    obtain ⟨m, hm⟩ := B.sampleData.cell_nonempty c
    exact ⟨m, by simpa only [Sbridge] using (Finset.mem_sdiff.mp hm).1⟩
  have hcellEq (c : Cell Head) : Sfixed c = Sbridge c := by
    simp only [Sfixed, Sbridge, PaperGuardCensus.rawCell,
      hpattern, hlo, hhi]
  have hrawPairBridge : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |((uniformOnFinset (Sbridge c) (hSbridge c)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
          (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (pairPower p q 1 1)| ≤
        rawError B.sampleData.n * pairWeight p q 1 1 := by
    intro c p hp q hq
    have hpW : p ∈ primeBand B.sampleData.n W := by
      simpa only [hBW] using hp
    have hqW : q ∈ (primeBand B.sampleData.n W).erase p := by
      simpa only [hBW] using hq
    have hpY := le_yNat_of_mem_primeBand hpW
    have hqY := le_yNat_of_mem_primeBand (Finset.mem_erase.mp hqW).2
    have hyPos : 0 < yNat B.sampleData.n :=
      (prime_of_mem_primeBand hpW).pos.trans_le hpY
    have hpqSq : p * q ≤ yNat B.sampleData.n ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hpY hqY
    have hpow : pairPower p q 1 1 ≤ yNat B.sampleData.n ^ 4 := by
      unfold pairPower
      norm_num
      exact hpqSq.trans (Nat.pow_le_pow_right hyPos (by omega : 2 ≤ 4))
    have hrawCell := hrawProfiles'.1 c p hpW q hqW 1 1 hpow
    have hrawCell' :
        |((uniformOnFinset (Sfixed c) (hSfixed c)).exponentialTilt
            (fun m ↦ valuationScore (primeBand B.sampleData.n W)
              (B.effectiveNatCoefficient xi) (Scale.L B.sampleData.n)
              (m : ℕ))).expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
            (pairPower p q 1 1)| ≤
          rawError B.sampleData.n * pairWeight p q 1 1 := by
      simpa only [Sfixed, PaperGuardCensus.rawCell, H, Alower, Cupper,
        PrimePowerCovariance.BoundedValuationLaw.widen_probability,
        PrimePowerCovariance.BoundedValuationLaw.widen_value,
        StructuredCellValuationLaw.valuationTilt_probability,
        StructuredCellValuationLaw.valuationTilt_value] using hrawCell
    have heq := uniformValuationTilt_expect_divInd_eq_of_finset_eq
      (Sfixed c) (Sbridge c) (hcellEq c) (hSfixed c) (hSbridge c)
      (primeBand B.sampleData.n W) (B.effectiveNatCoefficient xi)
      (Scale.L B.sampleData.n) (pairPower p q 1 1)
    have heq' :
        ((uniformOnFinset (Sfixed c) (hSfixed c)).exponentialTilt
            (fun m ↦ valuationScore (primeBand B.sampleData.n W)
              (B.effectiveNatCoefficient xi) (Scale.L B.sampleData.n)
              (m : ℕ))).expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) =
          ((uniformOnFinset (Sbridge c) (hSbridge c)).exponentialTilt
            (fun m ↦ valuationScore
              (primeBand B.sampleData.n B.sampleData.W)
              (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
            (fun m ↦ divInd (pairPower p q 1 1) (m : ℕ)) := by
      simpa only [hBW, BridgeData.L, Scale.L] using heq
    rw [← heq']
    exact hrawCell'
  have hrawSingleBridge : ∀ c p,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      |((uniformOnFinset (Sbridge c) (hSbridge c)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
          (fun m ↦ divInd p (m : ℕ)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
        rawError B.sampleData.n * singleWeight p 1 := by
    intro c p hp
    have hpW : p ∈ primeBand B.sampleData.n W := by
      simpa only [hBW] using hp
    have hrawCell := hrawProfiles'.2 c p hpW
    have hrawCell' :
        |((uniformOnFinset (Sfixed c) (hSfixed c)).exponentialTilt
            (fun m ↦ valuationScore (primeBand B.sampleData.n W)
              (B.effectiveNatCoefficient xi) (Scale.L B.sampleData.n)
              (m : ℕ))).expect (fun m ↦ divInd p (m : ℕ)) -
          PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          rawError B.sampleData.n * singleWeight p 1 := by
      simpa only [Sfixed, PaperGuardCensus.rawCell, H, Alower, Cupper,
        PrimePowerCovariance.BoundedValuationLaw.widen_probability,
        PrimePowerCovariance.BoundedValuationLaw.widen_value,
        StructuredCellValuationLaw.valuationTilt_probability,
        StructuredCellValuationLaw.valuationTilt_value] using hrawCell
    have heq := uniformValuationTilt_expect_divInd_eq_of_finset_eq
      (Sfixed c) (Sbridge c) (hcellEq c) (hSfixed c) (hSbridge c)
      (primeBand B.sampleData.n W) (B.effectiveNatCoefficient xi)
      (Scale.L B.sampleData.n) p
    have heq' :
        ((uniformOnFinset (Sfixed c) (hSfixed c)).exponentialTilt
            (fun m ↦ valuationScore (primeBand B.sampleData.n W)
              (B.effectiveNatCoefficient xi) (Scale.L B.sampleData.n)
              (m : ℕ))).expect (fun m ↦ divInd p (m : ℕ)) =
          ((uniformOnFinset (Sbridge c) (hSbridge c)).exponentialTilt
            (fun m ↦ valuationScore
              (primeBand B.sampleData.n B.sampleData.W)
              (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
            (fun m ↦ divInd p (m : ℕ)) := by
      simpa only [hBW, BridgeData.L, Scale.L] using heq
    rw [← heq']
    exact hrawCell'
  have hscoreAll (c : Cell Head) : ∀ m : Sbridge c,
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ K := by
    intro m
    simpa only [Sbridge, K, hBW] using
      (B.abs_unguardedCell_mediumScore_le xi c hCmax
        (by simpa only [hBW] using hW) hhiC hAcoef heta m)
  have hsmallBridge (c : Cell Head) : Real.exp (2 * K) *
      (B.sampleData.guards.card : ℝ) / ((Sbridge c).card : ℝ) ≤
        (1 : ℝ) / 2 := by
    have hcsmall := hsmallAll c
    simpa only [Sbridge, hpattern, hlo, hhi, hguards,
      PaperGuardCensus.rawCell] using hcsmall
  have hguardCell (c : Cell Head) :
      GuardDeletionSquarefreeProfiles.guardSquarefreeError
          (Sbridge c) B.sampleData.guards K B.sampleData.n ≤
        guardError B.sampleData.n := by
    have hsum := Finset.single_le_sum
      (fun c' hc' ↦ GuardDeletionSquarefreeProfiles.guardSquarefreeError_nonneg
        (PaperGuardCensus.rawCell Phead I B.sampleData.n c')
        (ledger B.sampleData.n).guards K B.sampleData.n)
      (Finset.mem_univ c)
    simpa only [Sbridge, guardError,
      Erdos390.Full.GuardSquarefreeErrorRate.canonicalGuardSquarefreeError,
      hpattern, hlo, hhi, hguards, PaperGuardCensus.rawCell] using hsum
  have hcoeff (c : Cell Head) : rawError B.sampleData.n +
      GuardDeletionSquarefreeProfiles.guardSquarefreeError
          (Sbridge c) B.sampleData.guards K B.sampleData.n ≤
        profileError B.sampleData.n := by
    dsimp only [profileError]
    exact add_le_add_right (hguardCell c) _
  constructor
  · intro c p hp q hq
    have hlocal := B.cellMediumLaw_squarefree_profiles_of_unguarded
      xi c (by simpa only [Sbridge] using hSbridge c)
      (by simpa only [Sbridge] using hscoreAll c)
      (by simpa only [Sbridge] using hsmallBridge c)
      (by simpa only [Sbridge] using hrawPairBridge c)
      (by simpa only [Sbridge] using hrawSingleBridge c)
    exact (hlocal.1 p hp q hq).trans
      (mul_le_mul_of_nonneg_right (hcoeff c) (pairWeight_nonneg p q 1 1))
  · intro c p hp
    have hlocal := B.cellMediumLaw_squarefree_profiles_of_unguarded
      xi c (by simpa only [Sbridge] using hSbridge c)
      (by simpa only [Sbridge] using hscoreAll c)
      (by simpa only [Sbridge] using hsmallBridge c)
      (by simpa only [Sbridge] using hrawPairBridge c)
      (by simpa only [Sbridge] using hrawSingleBridge c)
    exact (hlocal.2 p hp).trans
      (mul_le_mul_of_nonneg_right (hcoeff c) (singleWeight_nonneg p 1))





















/-! ### Exact finite-dimensional attachment to the arithmetic inverse -/



























/-! ### Reference-law row attachment

The literal global-tilt form of Lemma 7.5 is naturally obtained first for an
unguarded component mixture.  The actual bridge law is a guard-deleted
mixture with a residual physical tilt.  The next elementary estimate keeps
that identification issue outside the prime-power algebra: a weighted
prime-row comparison for the full and squarefree covariance matrices moves
the Lemma 7.5 estimate from an arbitrary reference law to the actual law.
The only moving-low loss is displayed explicitly as `rho / center i`.
-/





















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_3
theorem solution : Erdos390.RemainingAnalyticGoal001_011.{u_1, u_3} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_medium_signed_profiles
