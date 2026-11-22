-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_nonstepPower_inputs_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:13:59.271292+00:00
-- url     : https://prove2.me/submissions/6b53b86a-aeee-465c-b16b-8e6e8942601c

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
import Theorems.Thm_Erdos390_Full_FixedFiniteMixtureFullUniform_exists_boxIndependent_fixedFiniteMixture_primePower_transfer_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_eventually_canonicalPhysical_powerCorrection_row_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le_compact
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound




section
universe u_1 u_2
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_eventually_canonicalPhysical_powerCorrection_row : Erdos390.RemainingAnalyticGoal002_001.{u_1, u_2} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_eventually_canonicalPhysical_powerCorrection_row_compact
end
section
universe u_1
theorem Erdos390.Full.FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer : Erdos390.RemainingAnalyticGoal001_001.{u_1} := @Erdos390.Full.FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer_compact
end
section
universe u_1 u_2
theorem Erdos390.Full.PaperBridgeFit.BridgeData.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le : Erdos390.AnalyticCompactBatch003Goal002.{u_1, u_2} := @Erdos390.Full.PaperBridgeFit.BridgeData.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le_compact
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













end

end Erdos390.Full.GuardSquarefreeErrorRate

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



/-- The actual medium-prime score on a canonical unguarded raw cell has a
fixed-box bound independent of `n`, of the cell, and of the number of active
prime bands.  This is proved directly from the total valuation logarithm;
no probabilistic input is used. -/
theorem abs_canonicalRaw_mediumScore_le
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (hCmax : 1 ≤ Cmax)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (xi : B.ParamSpace) (hW : 1 < B.sampleData.W)
    {Acoef : ℝ} (hAcoef : 0 ≤ Acoef)
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ Acoef)
    (c : Cell Head) (m : rawCell P I B.sampleData.n c) :
    |valuationScore
        (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
      Acoef * PaperStatisticNorm.valuationLogCoefficient
        Cmax B.sampleData.W := by
  have hmpos : 0 < (m : ℕ) :=
    pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  have hmhi : (m : ℕ) ≤
      physicalBound (I.upper c.2) B.sampleData.n :=
    (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
  have hmC : (m : ℕ) ≤ physicalBound Cmax B.sampleData.n :=
    hmhi.trans (FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax c.2) B.sampleData.n)
  have hpW : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      B.sampleData.W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand hp).le
  have hetaNat : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi p| ≤ Acoef := by
    intro p hp
    rw [B.effectiveNatCoefficient_of_mem xi hp]
    exact heta ⟨p, hp⟩
  have hraw := ValuationTiltCell.abs_valuationScore_le_log_ratio
    (primeBand B.sampleData.n B.sampleData.W)
    (B.effectiveNatCoefficient xi) hmpos hmC hW hpW hAcoef B.L_pos hetaNat
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hcoef : 0 ≤ Acoef / B.L := div_nonneg hAcoef B.L_pos.le
  calc
    |valuationScore
        (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
      (Acoef / B.L) *
        (Real.log (physicalBound Cmax B.sampleData.n : ℝ) /
          Real.log (B.sampleData.W : ℝ)) := hraw
    _ ≤ (Acoef / B.L) *
        ((PaperStatisticNorm.physicalLogCoefficient Cmax * B.L) /
          Real.log (B.sampleData.W : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (PaperStatisticNorm.BridgeData.log_physicalBound_le B hCmax)
          hlogW.le) hcoef
    _ = Acoef * PaperStatisticNorm.valuationLogCoefficient
          Cmax B.sampleData.W := by
      unfold PaperStatisticNorm.valuationLogCoefficient
      field_simp [B.L_pos.ne', hlogW.ne']

/-- Elementary physical-log discharge of the logarithmic valuation envelope.
The constant is the same fixed-cutoff coefficient as in the score bound. -/
theorem valuationEnvelope_le_valuationLogCoefficient_mul_L
    (I : PhysicalIntervals) (Cmax : ℝ)
    (hupperOne : ∀ sigma, 1 ≤ I.upper sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (hW : 1 < B.sampleData.W) (c : Cell Head) :
    valuationEnvelope I B.sampleData.n B.sampleData.W c ≤
      PaperStatisticNorm.valuationLogCoefficient Cmax B.sampleData.W * B.L := by
  have hCmax : 1 ≤ Cmax :=
    (hupperOne c.2).trans (hupperMax c.2)
  have hnpos : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hnR : (0 : ℝ) < (B.sampleData.n : ℝ) := by exact_mod_cast hnpos
  have hupperPos : 0 < I.upper c.2 :=
    zero_lt_one.trans_le (hupperOne c.2)
  have hphysicalPos : (0 : ℝ) <
      physicalBound (I.upper c.2) B.sampleData.n := by
    have hnle : B.sampleData.n ≤
        physicalBound (I.upper c.2) B.sampleData.n := by
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (B.sampleData.n : ℝ) ≤
        I.upper c.2 * (B.sampleData.n : ℝ) by
          nlinarith [hnR.le, hupperOne c.2])
    exact_mod_cast hnpos.trans_le hnle
  have hphysicalMono :
      physicalBound (I.upper c.2) B.sampleData.n ≤
        physicalBound Cmax B.sampleData.n :=
    FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax c.2) B.sampleData.n
  have hlogMono :
      Real.log (physicalBound (I.upper c.2) B.sampleData.n : ℝ) ≤
        Real.log (physicalBound Cmax B.sampleData.n : ℝ) :=
    Real.log_le_log hphysicalPos (by exact_mod_cast hphysicalMono)
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  calc
    valuationEnvelope I B.sampleData.n B.sampleData.W c =
        Real.log (physicalBound (I.upper c.2) B.sampleData.n : ℝ) /
          Real.log (B.sampleData.W : ℝ) := rfl
    _ ≤ Real.log (physicalBound Cmax B.sampleData.n : ℝ) /
          Real.log (B.sampleData.W : ℝ) :=
      div_le_div_of_nonneg_right hlogMono hlogW.le
    _ ≤ (PaperStatisticNorm.physicalLogCoefficient Cmax * B.L) /
          Real.log (B.sampleData.W : ℝ) :=
      div_le_div_of_nonneg_right
        (PaperStatisticNorm.BridgeData.log_physicalBound_le B hCmax)
        hlogW.le
    _ = PaperStatisticNorm.valuationLogCoefficient Cmax
          B.sampleData.W * B.L := by
      unfold PaperStatisticNorm.valuationLogCoefficient
      ring



/-- Eventual canonical constructor specialization with every analytic input
to the finite guard theorem discharged.

For a fixed coefficient box and fixed physical cells, this theorem chooses a
single threshold independent of the later band partition, bridge data, tilt
point, and prime row.  Above that threshold the raw-cell density and the
half-mass inequality come from the proved ledger census; the score and
valuation-envelope bounds are the two elementary logarithmic estimates
above.  Thus the only hypotheses at the call site are exact structural
identification with `canonicalSampleData` and the genuine coefficient box. -/
theorem exists_eventually_canonicalGuardPowerCorrection_reference_bound
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hupperOne : ∀ sigma, 1 ≤ I.upper sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    let Cenv := PaperStatisticNorm.valuationLogCoefficient Cmax W
    let Kscore := Acoef * Cenv
    let Dguard := canonicalGuardPerturbationConstant P I Kscore
    ∃ N₀ : ℕ,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData Head Band) (xi : B.ParamSpace),
        N₀ ≤ B.sampleData.n →
        B.sampleData.W = W →
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData = canonicalSampleData (W := B.sampleData.W)
              P I (ledger B.sampleData.n) hsep hremaining →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          ∀ p : BandPrime B.sampleData.n B.sampleData.W,
            (p.1 : ℝ) *
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |((B.canonicalGuardedMediumReferenceLaw xi).covVV p.1 q.1 -
                    (B.canonicalGuardedMediumReferenceLaw xi).covII p.1 q.1) -
                  ((B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax
                      (fun c ↦ (hremaining c).mono
                        Finset.sdiff_subset)).covVV p.1 q.1 -
                    (B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax
                      (fun c ↦ (hremaining c).mono
                        Finset.sdiff_subset)).covII p.1 q.1)| ≤
              guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
                Dguard B.sampleData.n := by
  dsimp only
  let Cenv := PaperStatisticNorm.valuationLogCoefficient Cmax W
  let Kscore := Acoef * Cenv
  let Dguard := canonicalGuardPerturbationConstant P I Kscore
  have hCmax : 1 ≤ Cmax :=
    (hupperOne .minus).trans (hupperMax .minus)
  have hCenv : 0 ≤ Cenv := by
    simpa only [Cenv] using
      PaperStatisticNorm.valuationLogCoefficient_nonneg hCmax hW
  have hdensityEvent := eventually_rawCell_density P I
  have hsmallEvent :=
    GuardSquarefreeErrorRate.eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank ledger Kscore
  obtain ⟨Ndensity, hNdensity⟩ := Filter.eventually_atTop.1 hdensityEvent
  obtain ⟨Nsmall, hNsmall⟩ := Filter.eventually_atTop.1 hsmallEvent
  refine ⟨max Ndensity Nsmall, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW hsep hremaining
    hcanonical heta p
  have hNdensity' : Ndensity ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans hN
  have hNsmall' : Nsmall ≤ B.sampleData.n :=
    (Nat.le_max_right _ _).trans hN
  have hdensity := hNdensity B.sampleData.n hNdensity'
  have hsmallCensus := hNsmall B.sampleData.n hNsmall'
  have hWBridge : 1 < B.sampleData.W := by
    simpa only [hBW] using hW
  have hscore : ∀ c : Cell Head,
      ∀ m : rawCell P I B.sampleData.n c,
        |valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore := by
    intro c m
    have hraw := B.abs_canonicalRaw_mediumScore_le
      P I Cmax hCmax hupperMax xi hWBridge hAcoef heta c m
    simpa only [Kscore, Cenv, hBW] using hraw
  have hEnvelope : ∀ c : Cell Head,
      valuationEnvelope I B.sampleData.n B.sampleData.W c ≤
        Cenv * Scale.L B.sampleData.n := by
    intro c
    have hraw := B.valuationEnvelope_le_valuationLogCoefficient_mul_L
      I Cmax hupperOne hupperMax hWBridge c
    simpa only [Cenv, hBW, BridgeData.L, Scale.L] using hraw
  exact B.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
    P I Cmax (ledger B.sampleData.n) hsep hremaining hcanonical xi
    hupperMax hWBridge hCenv hscore hsmallCensus hdensity hEnvelope p











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalRawLemma75 -/
section


/-!
# Attaching the raw canonical bridge mixture to Lemma 7.5

The unguarded reference law used in the canonical guard comparison is a
finite mixture of the literal structured-cell valuation tilts.  Its mixture
weights are the actual post-tilt bridge weights, but Lemma 7.5 is uniform in
those weights.  This file records the exact specialization, including the
order of choices: the prime-power constant is selected before the cutoff and
coefficient box, and the eventual threshold is uniform in the bridge data,
tilt point, and component weights.
-/

open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperGuardCensus

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- The canonical raw reference mixture satisfies the literal five-field
prime-power transfer of Lemma 7.5.  No condition on the post-tilt component
weights is needed: the fixed-finite-mixture theorem is uniform over every
finite probability on `Cell Head`.

The returned remainder is common to all five estimates and retains the
moving-low rate `epsilon(n) * log L(n) -> 0`. -/
theorem boxIndependent_canonicalRaw_primePower_transfer
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax) :
    0 < FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant ∧
      ∀ W : ℕ, 1 < W →
        (∀ h, ∀ p ∈ (P h).primes, p ≤ W) →
      ∀ Acoef : ℝ, 0 ≤ Acoef →
      ∃ epsilon : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon n) ∧
        Tendsto epsilon atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ,
          ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
            (B : BridgeData Head Band) (xi : B.ParamSpace),
            N₀ ≤ B.sampleData.n →
            B.sampleData.W = W →
            (∀ p : BandPrime B.sampleData.n B.sampleData.W,
              |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
            ∀ hS : ∀ c : Cell Head,
              (rawCell P I B.sampleData.n c).Nonempty,
              PaperPrimePowerLemma75.PrimePowerTransferBounds
                (B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax hS)
                B.sampleData.n B.sampleData.W
                  FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
                  (epsilon B.sampleData.n) := by
  let H : Cell Head → HeadPattern.Pattern := fun c ↦ P c.1
  let Alower : Cell Head → ℝ := fun c ↦ I.lower c.2
  let Cupper : Cell Head → ℝ := fun c ↦ I.upper c.2
  have hCmax : 0 < Cmax :=
    (I.lower_pos .minus).trans
      ((I.lower_lt_upper .minus).trans_le (hupperMax .minus))
  obtain ⟨hCpow, hmain⟩ :=
    FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer
      H Alower Cupper Cmax
      (fun c ↦ I.lower_pos c.2)
      (fun c ↦ I.lower_lt_upper c.2)
      (fun c ↦ lt_trans (I.lower_pos c.2) (I.lower_lt_upper c.2))
      hCmax (fun c ↦ hupperMax c.2)
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  refine ⟨hCpow, ?_⟩
  intro W hW hsupport Acoef hAcoef
  obtain ⟨epsilon, hepsilon0, hepsilonT, hepsilonRate, N₀, hN₀⟩ :=
    hmain W hW (fun c ↦ hsupport c.1) Acoef hAcoef
  refine ⟨epsilon, hepsilon0, hepsilonT, hepsilonRate, N₀, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW heta hS
  subst W
  have hetaNat : ∀ z ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi z| ≤ Acoef := by
    intro z hz
    rw [B.effectiveNatCoefficient_of_mem xi hz]
    exact heta ⟨z, hz⟩
  obtain ⟨_hSauto, hbounds⟩ :=
    hN₀ (B.effectiveNatCoefficient xi) hN hetaNat
  have hbound := hbounds hS
    (tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi))
  simpa [H, Alower, Cupper, rawCell,
    canonicalRawMediumReferenceLaw, canonicalRawMediumComponentLaw]
    using hbound



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBridgeCanonicalPowerCorrectionTriangle -/
section


/-!
# The terminal canonical prime-power correction triangle

This module joins the two independently proved finite comparisons used in
Lemma 8.4:

* the residual physical tilt compares the actual bridge law with the
  medium-only law; and
* literal guard deletion compares that same medium-only law with the raw
  unguarded canonical reference law.

The intermediate laws are definitionally equal and carry exactly the same
post-tilt component weights.  The triangle therefore retains all
between-component covariance terms and produces the literal weighted
`VV-II` row required by the full-versus-squarefree connector.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperGuardCensus GuardedUniformCell
open StructuredCells ValuationScoreDomination PrimeSums

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The intermediate law in the physical comparison is literally the
guarded medium law in the canonical guard comparison. -/
theorem physicalMediumReferenceLaw_eq_canonicalGuardedMediumReferenceLaw
    [Nonempty Head] (xi : B.ParamSpace) :
    B.physicalMediumReferenceLaw xi =
      B.canonicalGuardedMediumReferenceLaw xi := by
  rfl

/-- Algebraic weighted-row triangle through the literal medium reference
law.  This connector is useful when the two finite sides have already been
instantiated by their respective eventual constructor theorems. -/
theorem actual_powerCorrection_reference_weightedRow_le_of_two_sides
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    {rhoPhysical rhoReference : ℝ}
    (hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1)| ≤
        rhoPhysical)
    (hreference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| ≤
        rhoReference) :
    ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| ≤
        rhoPhysical + rhoReference := by
  intro p
  have hpoint (q : BandPrime B.sampleData.n B.sampleData.W) :
      |((B.actualValuationLaw xi).covVV p.1 q.1 -
          (B.actualValuationLaw xi).covII p.1 q.1) -
        (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| ≤
      |((B.actualValuationLaw xi).covVV p.1 q.1 -
          (B.actualValuationLaw xi).covII p.1 q.1) -
        ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.physicalMediumReferenceLaw xi).covII p.1 q.1)| +
      |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
        (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| := by
    let a := (B.actualValuationLaw xi).covVV p.1 q.1 -
      (B.actualValuationLaw xi).covII p.1 q.1
    let b := (B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
      (B.physicalMediumReferenceLaw xi).covII p.1 q.1
    let c := referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1
    change |a - c| ≤ |a - b| + |b - c|
    rw [show a - c = (a - b) + (b - c) by ring]
    exact abs_add_le _ _
  have hsum :
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| ≤
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) +
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
          (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| := by
    calc
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (|((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1)| +
          |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)|) :=
        Finset.sum_le_sum fun q hq ↦ hpoint q
      _ = _ := Finset.sum_add_distrib
  have hp0 : 0 ≤ (p.1 : ℝ) := by positivity
  calc
    (p.1 : ℝ) * ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| ≤
      (p.1 : ℝ) *
        ((∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) +
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)|) :=
      mul_le_mul_of_nonneg_left hsum hp0
    _ = (p.1 : ℝ) *
          (∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |((B.actualValuationLaw xi).covVV p.1 q.1 -
                (B.actualValuationLaw xi).covII p.1 q.1) -
              ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
                (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) +
        (p.1 : ℝ) *
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
                (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
              (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| := by
      ring
    _ ≤ rhoPhysical + rhoReference := add_le_add (hphysical p) (hreference p)









end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalNonstepPowerInputsEventually -/
section


/-!
# Canonical inputs for the non-step full slow row

This file exports the two objects that the literal non-step ledger needs,
rather than only their earlier step-function contraction:

* Lemma 7.5 for the unguarded canonical raw reference law; and
* the reciprocal weighted `VV-II` row comparing the final actual law with
  that same reference law.

The prime-power constant is chosen before `W` and the later coefficient
box.  Both analytic remainders retain the sharp moving-low rate after
multiplication by `log L`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperGuardCensus

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]





/-- Box-independent canonical raw inputs for the exact non-step slow-row
ledgers.  The eventual threshold is uniform in the band type, bridge data,
tilt point, and component weights. -/
theorem boxIndependent_canonicalRaw_nonstepPower_inputs
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, Ledger n Cprom Cbank) :
    0 < FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant ∧
      ∀ W : ℕ, 1 < W →
        (∀ h, ∀ p ∈ (P h).primes, p ≤ W) →
      ∀ Acoef : ℝ, 0 ≤ Acoef →
      ∀ Aphys : ℝ, 0 ≤ Aphys →
      ∃ epsilon75 : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon75 n) ∧
        Tendsto epsilon75 atTop (nhds 0) ∧
        Tendsto
          (fun n : ℕ ↦ epsilon75 n * Real.log (Scale.L n))
          atTop (nhds 0) ∧
        Tendsto
          (fun n : ℕ ↦
            canonicalNonstepPowerCorrection
              P I Cmax Cprom Cbank W Acoef Aphys n *
                Real.log (Scale.L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ,
          ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
            (B : BridgeData Head Band) (xi : B.ParamSpace),
            N₀ ≤ B.sampleData.n →
            B.sampleData.W = W →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell P I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              B.sampleData = canonicalSampleData (W := B.sampleData.W)
                  P I (ledger B.sampleData.n) hsep hremaining →
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              |xi MomentCoord.physical| ≤ Aphys →
              let hS : ∀ c : Cell Head,
                  (rawCell P I B.sampleData.n c).Nonempty :=
                fun c ↦ (hremaining c).mono Finset.sdiff_subset
              let referenceLaw :=
                B.canonicalRawMediumReferenceLaw
                  P I Cmax xi hupperMax hS
              PaperPrimePowerLemma75.PrimePowerTransferBounds
                  referenceLaw B.sampleData.n B.sampleData.W
                    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
                    (epsilon75 B.sampleData.n) ∧
                ∀ p : BandPrime B.sampleData.n B.sampleData.W,
                  (p.1 : ℝ) *
                    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                      |((B.actualValuationLaw xi).covVV p.1 q.1 -
                          (B.actualValuationLaw xi).covII p.1 q.1) -
                        (referenceLaw.covVV p.1 q.1 -
                          referenceLaw.covII p.1 q.1)| ≤
                    canonicalNonstepPowerCorrection
                      P I Cmax Cprom Cbank W Acoef Aphys
                        B.sampleData.n := by
  obtain ⟨hCpow, h75main⟩ :=
    boxIndependent_canonicalRaw_primePower_transfer P I Cmax hupperMax
  refine ⟨hCpow, ?_⟩
  intro W hW hsupport Acoef hAcoef Aphys hAphys0
  obtain ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
      N75, hN75⟩ := h75main W hW hsupport Acoef hAcoef
  have hupperOne : ∀ sigma, 1 ≤ I.upper sigma := fun sigma ↦
    (hlowerOne sigma).trans (I.lower_lt_upper sigma).le
  obtain ⟨Nguard, hNguard⟩ :=
    exists_eventually_canonicalGuardPowerCorrection_reference_bound
      P I Cmax hupperOne hupperMax Cprom Cbank ledger
        W hW Acoef hAcoef
  have hphysicalMain :=
    exists_eventually_canonicalPhysical_powerCorrection_row
      P I Cmax hlowerOne hupperMax Cprom Cbank ledger
        W hW Acoef Aphys hAcoef hAphys0
  dsimp only at hphysicalMain
  obtain ⟨_hGphys, hphysicalRate, Nphysical, hNphysical⟩ :=
    hphysicalMain
  have hCmax : 1 ≤ Cmax :=
    (hupperOne .minus).trans (hupperMax .minus)
  have hCenv : 0 ≤
      PaperStatisticNorm.valuationLogCoefficient Cmax W :=
    PaperStatisticNorm.valuationLogCoefficient_nonneg hCmax hW
  have hDguard : 0 ≤ canonicalGuardPerturbationConstant P I
      (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W) :=
    canonicalGuardPerturbationConstant_nonneg P I _
  have hguardRate :=
    tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
      Cprom Cbank hCenv hDguard
  have htotalRate : Tendsto
      (fun n : ℕ ↦
        canonicalNonstepPowerCorrection
          P I Cmax Cprom Cbank W Acoef Aphys n *
            Real.log (Scale.L n)) atTop (nhds 0) := by
    simpa only [canonicalNonstepPowerCorrection, add_mul, zero_add] using
      hphysicalRate.add hguardRate
  refine ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
    htotalRate, max N75 (max Nguard Nphysical), ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW hsep hremaining
    hcanonical heta hphys
  have hN75' : N75 ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans hN
  have hNguard' : Nguard ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right N75 _).trans hN)
  have hNphysical' : Nphysical ≤ B.sampleData.n :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right N75 _).trans hN)
  let hS : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c).Nonempty :=
    fun c ↦ (hremaining c).mono Finset.sdiff_subset
  let referenceLaw :=
    B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax hS
  have h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds
      referenceLaw B.sampleData.n B.sampleData.W
        FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
        (epsilon75 B.sampleData.n) := by
    simpa only [referenceLaw, hS] using
      hN75 B xi hN75' hBW heta hS
  have hphysical := hNphysical B xi hNphysical' hBW hsep hremaining
    hcanonical heta hphys
  have hguardRaw := hNguard B xi hNguard' hBW hsep hremaining
    hcanonical heta
  have hguard : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| ≤
        guardPowerCorrectionWeightedMajorant Cprom Cbank
          (PaperStatisticNorm.valuationLogCoefficient Cmax W)
          (canonicalGuardPerturbationConstant P I
            (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W))
          B.sampleData.n := by
    intro p
    simpa only [referenceLaw, hS,
      physicalMediumReferenceLaw_eq_canonicalGuardedMediumReferenceLaw] using
        hguardRaw p
  have hpowerRow :=
    B.actual_powerCorrection_reference_weightedRow_le_of_two_sides
      xi referenceLaw hphysical hguard
  exact ⟨h75, by
    simpa only [referenceLaw, hS,
      canonicalNonstepPowerCorrection, hBW] using hpowerRow⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2
theorem solution : Erdos390.RemainingAnalyticGoal001_008.{u_1, u_2} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_nonstepPower_inputs
