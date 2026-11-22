-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:14:22.694978+00:00
-- url     : https://prove2.me/submissions/37572abd-c684-4caa-9108-a308a25f2989

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
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualComponent_squarefree_profiles_of_medium
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_boxIndependent_actual_medium_signed_profiles_compact
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound


section
universe u_1 u_3
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_medium_signed_profiles : Erdos390.RemainingAnalyticGoal001_011.{u_1, u_3} := @Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_medium_signed_profiles_compact
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

























/-- The actual guard-deleted cell endpoint is positive. -/
theorem cell_hi_pos (c : Cell Head) :
    0 < B.sampleData.hi c.2 := by
  obtain ⟨m, hm⟩ := B.sampleData.cell_nonempty c
  let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
  have hmle : m ≤ B.sampleData.hi c.2 := by
    simpa only [sample, StructuredSampleData.value,
      StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample
  have hmpos : 0 < m := by
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  exact hmpos.trans_le hmle











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

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

/-- After deleting the concrete guard ledger, every fixed head/physical cell
still retains a fixed positive fraction of its proved raw density.  The
constant `1/4` is uniform over the finite family of cells and is stated at
the literal finite-`n` cardinality level. -/
theorem eventually_guarded_rawCell_density
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      PaperScaleMarkedCell.paperCellDensity (P c.1)
          (I.lower c.2) (I.upper c.2) * (n : ℝ) / 4 ≤
        ((rawCell P I n c \ (G n).guards).card : ℝ) := by
  have hdensity := eventually_rawCell_density P I
  have hguardRatio :=
    eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank G 0
  filter_upwards [hdensity, hguardRatio, eventually_gt_atTop 0] with
      n hdens hratio hn c
  let density := PaperScaleMarkedCell.paperCellDensity (P c.1)
    (I.lower c.2) (I.upper c.2)
  let S := rawCell P I n c
  let R := S \ (G n).guards
  have hdensityPos : 0 < density := by
    exact PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    have hmain : 0 < density * (n : ℝ) / 2 := by positivity
    exact hmain.trans_le (by simpa only [density, S] using hdens c)
  have hratio' : ((G n).guards.card : ℝ) / (S.card : ℝ) ≤
      (1 : ℝ) / 2 := by
    have hc := hratio c
    norm_num at hc
    simpa only [S] using hc
  have hguard : ((G n).guards.card : ℝ) ≤ (S.card : ℝ) / 2 := by
    have := (div_le_iff₀ hSpos).mp hratio'
    nlinarith
  have hcardNat : S.card ≤ R.card + (G n).guards.card := by
    simpa only [R] using
      (Finset.card_le_card_sdiff_add_card
        (s := S) (t := (G n).guards))
  have hcardReal : (S.card : ℝ) ≤ (R.card : ℝ) +
      ((G n).guards.card : ℝ) := by exact_mod_cast hcardNat
  have hraw : density * (n : ℝ) / 2 ≤ (S.card : ℝ) := by
    simpa only [density, S] using hdens c
  have : density * (n : ℝ) / 4 ≤ (R.card : ℝ) := by
    nlinarith
  simpa only [density, S, R] using this

/-- Endpoint-normalized form of `eventually_guarded_rawCell_density`.  Each
fixed cell gets the explicit positive density
`paperCellDensity/(4*upper)`; no minimum over a varying family is used. -/
theorem eventually_guarded_rawCell_endpoint_density
    {Head : Type*} [Fintype Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank) :
    ∀ᶠ n : ℕ in atTop, ∀ c : PaperBridgeFit.Cell Head,
      let rho := PaperScaleMarkedCell.paperCellDensity (P c.1)
        (I.lower c.2) (I.upper c.2) / (4 * I.upper c.2)
      0 < rho ∧
        rho * (physicalBound (I.upper c.2) n : ℝ) ≤
          ((rawCell P I n c \ (G n).guards).card : ℝ) := by
  have hdensity := eventually_guarded_rawCell_density P I Cprom Cbank G
  filter_upwards [hdensity] with n hdens c
  let density := PaperScaleMarkedCell.paperCellDensity (P c.1)
    (I.lower c.2) (I.upper c.2)
  let upper := I.upper c.2
  let rho := density / (4 * upper)
  have hdensityPos : 0 < density := by
    exact PaperScaleMarkedCell.paperCellDensity_pos
      (P c.1) (I.lower_lt_upper c.2)
  have hupperPos : 0 < upper := by
    exact (I.lower_pos c.2).trans (I.lower_lt_upper c.2)
  have hrho : 0 < rho := by
    exact div_pos hdensityPos (mul_pos (by norm_num) hupperPos)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hbound : (physicalBound upper n : ℝ) ≤ upper * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hupperPos.le hn0)
  have hscaled : rho * (physicalBound upper n : ℝ) ≤
      density * (n : ℝ) / 4 := by
    calc
      rho * (physicalBound upper n : ℝ) ≤ rho * (upper * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound hrho.le
      _ = density * (n : ℝ) / 4 := by
        dsimp only [rho]
        field_simp [hupperPos.ne']
  refine ⟨hrho, hscaled.trans ?_⟩
  simpa only [density, upper] using hdens c









end

end Erdos390.Full.GuardSquarefreeErrorRate

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











/-- The exponential reciprocal fallback used by the physical second tilt is
bounded by the same fixed effective-prime box constant as the raw medium
score.  In particular the ceiling has no dependence on `n` or on a moving
band cell. -/
theorem mediumFallbackExponent_le [Nonempty Head]
    (c : Cell Head) {C A : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W) (hA : 0 ≤ A)
    (hhi : B.sampleData.hi c.2 ≤
      physicalBound C B.sampleData.n) :
    (A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)) ≤
      A * PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W := by
  have hhiPos : (0 : ℝ) < B.sampleData.hi c.2 := by
    exact_mod_cast B.cell_hi_pos c
  have hboundPos : (0 : ℝ) < physicalBound C B.sampleData.n := by
    have hn : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
    have hnle : B.sampleData.n ≤ physicalBound C B.sampleData.n := by
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (B.sampleData.n : ℝ) ≤
        C * (B.sampleData.n : ℝ) by
          nlinarith [show (0 : ℝ) ≤ (B.sampleData.n : ℝ) by positivity])
    exact_mod_cast hn.trans_le hnle
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hlogHi : Real.log (B.sampleData.hi c.2 : ℝ) ≤
      PaperStatisticNorm.physicalLogCoefficient C * B.L := by
    exact (Real.log_le_log hhiPos (by exact_mod_cast hhi)).trans
      (PaperStatisticNorm.BridgeData.log_physicalBound_le B hC)
  have hratio :
      Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ) ≤
        (PaperStatisticNorm.physicalLogCoefficient C * B.L) /
          Real.log (B.sampleData.W : ℝ) :=
    div_le_div_of_nonneg_right hlogHi hlogW.le
  calc
    (A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)) ≤
        (A / B.L) *
          ((PaperStatisticNorm.physicalLogCoefficient C * B.L) /
            Real.log (B.sampleData.W : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (div_nonneg hA B.L_pos.le)
    _ = A * PaperStatisticNorm.valuationLogCoefficient C
          B.sampleData.W := by
      unfold PaperStatisticNorm.valuationLogCoefficient
      field_simp [B.L_pos.ne', hlogW.ne']







/-- Uniform signed profiles for the literal full component laws.  This is
the finite-`n` attachment needed before taking the exact sigma mixture: raw
marked-cell asymptotics, guard deletion, and the physical second tilt are
all included in one error which is `o(1 / log L)`.

Every constant is selected from `Phead`, the two fixed physical intervals,
the fixed cutoff, and the preselected coefficient box.  No constant depends
on `n`, on a moving band cell, or on a subsequently chosen bridge law. -/
theorem exists_boxIndependent_actual_component_signed_profiles
    [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∀ W : ℕ, 1 < W →
      (∀ h, ∀ p ∈ (Phead h).primes, p ≤ W) →
    ∀ Acoef Aphys : ℝ, 0 ≤ Acoef → 0 ≤ Aphys →
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
          |xi MomentCoord.physical| ≤ Aphys →
          B.sampleData.W = W →
          (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
            ∀ q, q ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
            |(B.actualComponentValuationLaw xi c).probability.expect
                (fun m ↦ divInd (pairPower p q 1 1)
                  ((B.actualComponentValuationLaw xi c).value m)) -
              PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
                (pairPower p q 1 1)| ≤
              profileError B.sampleData.n * pairWeight p q 1 1) ∧
          (∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
            |(B.actualComponentValuationLaw xi c).probability.expect
                (fun m ↦ divInd p
                  ((B.actualComponentValuationLaw xi c).value m)) -
              PaperScaleMarkedCell.paperDivisibilityMain
                B.sampleData.n p| ≤
              profileError B.sampleData.n * singleWeight p 1) := by
  intro W hW hsupport Acoef Aphys hAcoef hAphys0
  have hupperOne : ∀ sigma, 1 ≤ I.upper sigma := by
    intro sigma
    exact (hlowerOne sigma).trans (I.lower_lt_upper sigma).le
  have hCmax : 1 ≤ Cmax :=
    (hupperOne .minus).trans (hupperMax .minus)
  obtain ⟨mediumError, hmedium0, hmediumT, hmediumRate,
      Nmedium, hmedium⟩ :=
    exists_boxIndependent_actual_medium_signed_profiles
      Phead I Cmax hupperOne hupperMax Cprom Cbank ledger
        W hW hsupport Acoef hAcoef
  let K := Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W
  let rhoCell : Cell Head → ℝ := fun c ↦
    PaperScaleMarkedCell.paperCellDensity (Phead c.1)
      (I.lower c.2) (I.upper c.2) / (4 * I.upper c.2)
  let Gcell : Cell Head → ℝ := fun c ↦ Real.exp (2 * K) / rhoCell c
  let Gtotal : ℝ := ∑ c : Cell Head, Gcell c
  let physicalConstant : ℝ :=
    4 * Aphys * Real.log Cmax * Gtotal
  let physicalError : ℕ → ℝ := fun n ↦ physicalConstant / Scale.L n
  let profileError : ℕ → ℝ := fun n ↦ mediumError n + physicalError n
  have hrhoPos (c : Cell Head) : 0 < rhoCell c := by
    dsimp only [rhoCell]
    exact div_pos
      (PaperScaleMarkedCell.paperCellDensity_pos
        (Phead c.1) (I.lower_lt_upper c.2))
      (mul_pos (by norm_num)
        ((I.lower_pos c.2).trans (I.lower_lt_upper c.2)))
  have hGcell0 (c : Cell Head) : 0 ≤ Gcell c := by
    dsimp only [Gcell]
    exact div_nonneg (Real.exp_pos _).le (hrhoPos c).le
  have hGtotal0 : 0 ≤ Gtotal := by
    exact Finset.sum_nonneg fun c _ ↦ hGcell0 c
  have hlogC0 : 0 ≤ Real.log Cmax := Real.log_nonneg hCmax
  have hphysicalConstant0 : 0 ≤ physicalConstant := by
    dsimp only [physicalConstant]
    positivity
  have hL0 (n : ℕ) : 0 ≤ Scale.L n := by
    cases n with
    | zero => norm_num [Scale.L]
    | succ n =>
        exact Real.log_nonneg (by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hphysical0 (n : ℕ) : 0 ≤ physicalError n := by
    exact div_nonneg hphysicalConstant0 (hL0 n)
  have hprofile0 (n : ℕ) : 0 ≤ profileError n :=
    add_nonneg (hmedium0 n) (hphysical0 n)
  have hLTop : Filter.Tendsto Scale.L Filter.atTop Filter.atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInvL : Filter.Tendsto (fun n : ℕ ↦ (Scale.L n)⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLTop
  have hphysicalT : Filter.Tendsto physicalError Filter.atTop (nhds 0) := by
    have hraw :=
      (tendsto_const_nhds : Filter.Tendsto
        (fun _n : ℕ ↦ physicalConstant) Filter.atTop
          (nhds physicalConstant)).mul hInvL
    have hzero : Filter.Tendsto
        (fun n : ℕ ↦ physicalConstant * (Scale.L n)⁻¹)
          Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hraw
    apply hzero.congr'
    filter_upwards with n
    dsimp only [physicalError]
    rw [div_eq_mul_inv]
  have hlogLDivL : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Scale.L n) / Scale.L n)
        Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hphysicalRate : Filter.Tendsto
      (fun n : ℕ ↦ physicalError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    have hraw :=
      (tendsto_const_nhds : Filter.Tendsto
        (fun _n : ℕ ↦ physicalConstant) Filter.atTop
          (nhds physicalConstant)).mul hlogLDivL
    have hzero : Filter.Tendsto
        (fun n : ℕ ↦ physicalConstant *
          (Real.log (Scale.L n) / Scale.L n))
          Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hraw
    apply hzero.congr'
    filter_upwards with n
    dsimp only [physicalError]
    ring
  have hprofileT : Filter.Tendsto profileError Filter.atTop (nhds 0) := by
    simpa only [profileError, add_zero] using hmediumT.add hphysicalT
  have hprofileRate : Filter.Tendsto
      (fun n : ℕ ↦ profileError n * Real.log (Scale.L n))
        Filter.atTop (nhds 0) := by
    simpa only [profileError, add_mul, add_zero] using
      hmediumRate.add hphysicalRate
  have hdensityEvent :=
    Erdos390.Full.GuardSquarefreeErrorRate.eventually_guarded_rawCell_endpoint_density
      Phead I Cprom Cbank ledger
  obtain ⟨Ndensity, hNdensity⟩ := Filter.eventually_atTop.1 hdensityEvent
  have hepsilonT : Filter.Tendsto
      (fun n : ℕ ↦ 8 * (Aphys * Real.log Cmax / Scale.L n))
        Filter.atTop (nhds 0) := by
    have hraw :=
      (tendsto_const_nhds : Filter.Tendsto
        (fun _n : ℕ ↦ 8 * (Aphys * Real.log Cmax)) Filter.atTop
          (nhds (8 * (Aphys * Real.log Cmax)))).mul hInvL
    have hzero : Filter.Tendsto
        (fun n : ℕ ↦ (8 * (Aphys * Real.log Cmax)) *
          (Scale.L n)⁻¹) Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using hraw
    apply hzero.congr'
    filter_upwards with n
    ring
  have hsmallEvent : ∀ᶠ n : ℕ in Filter.atTop,
      8 * (Aphys * Real.log Cmax / Scale.L n) ≤ 1 :=
    hepsilonT.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨Nsmall, hNsmall⟩ := Filter.eventually_atTop.1 hsmallEvent
  let N₀ := max Nmedium (max Ndensity Nsmall)
  refine ⟨profileError, hprofile0, hprofileT, hprofileRate, N₀, ?_⟩
  intro Band _instBand _instBandDec B xi hN hpattern hlo hhi hguards
    heta hphys hBW
  have hNmedium : Nmedium ≤ B.sampleData.n := by
    dsimp only [N₀] at hN
    omega
  have hNdensity' : Ndensity ≤ B.sampleData.n := by
    dsimp only [N₀] at hN
    omega
  have hNsmall' : Nsmall ≤ B.sampleData.n := by
    dsimp only [N₀] at hN
    omega
  have hmediumProfiles := hmedium B xi hNmedium hpattern hlo hhi
    hguards heta hBW
  have hdensityAll := hNdensity B.sampleData.n hNdensity'
  have hsmall : 8 * (Aphys * Real.log Cmax / B.L) ≤ 1 := by
    simpa only [BridgeData.L, Scale.L] using
      hNsmall B.sampleData.n hNsmall'
  have hhiC : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound Cmax B.sampleData.n := by
    intro sigma
    rw [hhi sigma]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperMax sigma) B.sampleData.n
  have hWBridge : 1 < B.sampleData.W := by simpa only [hBW] using hW
  have hphysicalErrorBound (c : Cell Head) :
      let epsilon := Aphys * Real.log Cmax / B.L
      let G := Real.exp (2 * ((Acoef / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rhoCell c
      4 * epsilon * G ≤ physicalError B.sampleData.n := by
    dsimp only
    let exponent := (Acoef / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ))
    let Gactual := Real.exp (2 * exponent) / rhoCell c
    have hexponent : exponent ≤ K := by
      simpa only [exponent, K, hBW] using
        B.mediumFallbackExponent_le c hCmax hWBridge hAcoef (hhiC c.2)
    have hGactual : Gactual ≤ Gcell c := by
      dsimp only [Gactual, Gcell]
      exact div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hexponent (by norm_num)))
        (hrhoPos c).le
    have hGcellTotal : Gcell c ≤ Gtotal := by
      exact Finset.single_le_sum (fun d _ ↦ hGcell0 d) (Finset.mem_univ c)
    have hfactor0 : 0 ≤ 4 * (Aphys * Real.log Cmax / B.L) := by
      exact mul_nonneg (by norm_num)
        (div_nonneg (mul_nonneg hAphys0 hlogC0) B.L_pos.le)
    calc
      4 * (Aphys * Real.log Cmax / B.L) * Gactual ≤
          4 * (Aphys * Real.log Cmax / B.L) * Gcell c :=
        mul_le_mul_of_nonneg_left hGactual hfactor0
      _ ≤ 4 * (Aphys * Real.log Cmax / B.L) * Gtotal :=
        mul_le_mul_of_nonneg_left hGcellTotal hfactor0
      _ = physicalError B.sampleData.n := by
        dsimp only [physicalError, physicalConstant, BridgeData.L, Scale.L]
        ring
  have hcoeff (c : Cell Head) :
      mediumError B.sampleData.n +
          4 * (Aphys * Real.log Cmax / B.L) *
            (Real.exp (2 * ((Acoef / B.L) *
              (Real.log (B.sampleData.hi c.2 : ℝ) /
                Real.log (B.sampleData.W : ℝ)))) / rhoCell c) ≤
        profileError B.sampleData.n := by
    dsimp only [profileError]
    exact add_le_add_right (hphysicalErrorBound c) _
  have hlocal (c : Cell Head) := by
    have hdensityC := hdensityAll c
    have hrho : 0 < rhoCell c := hrhoPos c
    have hcard : rhoCell c * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ) := by
      simpa only [rhoCell, StructuredSampleData.cellFinset,
        PaperGuardCensus.rawCell, hpattern, hlo, hhi, hguards] using
          hdensityC.2
    have hKphys : ∀ m : B.sampleData.SampleAt c,
        |B.physicalScore ⟨c, m⟩| ≤ Real.log Cmax := by
      intro m
      exact B.abs_physicalScore_le_log_upperBound I hlowerOne hupperMax
        hlo hhi ⟨c, m⟩
    exact B.actualComponent_squarefree_profiles_of_medium xi c
      hAcoef hWBridge hrho hcard heta hAphys0 hlogC0 hphys hKphys hsmall
      (hmediumProfiles.1 c) (hmediumProfiles.2 c)
  constructor
  · intro c p hp q hq
    exact (hlocal c).1 p hp q hq |>.trans
      (mul_le_mul_of_nonneg_right (hcoeff c)
        (pairWeight_nonneg p q 1 1))
  · intro c p hp
    exact (hlocal c).2 p hp |>.trans
      (mul_le_mul_of_nonneg_right (hcoeff c)
        (singleWeight_nonneg p 1))

















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
theorem solution : Erdos390.RemainingAnalyticGoal001_010.{u_1, u_3} := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles
