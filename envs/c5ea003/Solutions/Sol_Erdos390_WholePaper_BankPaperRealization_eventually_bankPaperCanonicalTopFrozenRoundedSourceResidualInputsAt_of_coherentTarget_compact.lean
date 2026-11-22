-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.716497+00:00
-- url     : https://prove2.me/submissions/cdfc9d0b-365e-4e55-87ce-9481607d4bf0

import Definitions.Def_erdos390_remaining_analytic_propositions_004
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
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_eventually_roughCanonicalBalancedNonsmoothBounds_compact
import Theorems.Thm_Erdos390_WholePaper_eventually_roughCanonicalActiveIntrinsicRawBroadSurplus_compact
import Theorems.Thm_Erdos390_WholePaper_fullCentralAnchors_completeRoughLabel_injective_of_ne_one



section
theorem Erdos390.WholePaper.eventually_roughCanonicalActiveIntrinsicRawBroadSurplus : Erdos390.RemainingAnalyticGoal008_006 := @Erdos390.WholePaper.eventually_roughCanonicalActiveIntrinsicRawBroadSurplus_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalBalancedNonsmoothBounds : Erdos390.RemainingAnalyticGoal004_016 := @Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalBalancedNonsmoothBounds_compact
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

/- Source module: Erdos390.Full.PaperBridgeFit -/
section


/-!
# The finite arithmetic data in the bridge fit

This file instantiates the nonlinear finite-family layer with the actual
objects appearing in Lemmas 8.5--8.6 and Proposition 8.7: guarded smooth
structured cells, arithmetic prime bands, valuation statistics, the physical
logarithm, centered head indicators, and the compensated slow score.

The sample is the tagged disjoint union of the paper's cells.  Tagging is the
formal counterpart of the disjointification performed before normalization;
the underlying integer remains available as `Sample.value`.

All statements in this file are finite identities.  Asymptotic marked-smooth
estimates are not silently inserted as hypotheses equivalent to the desired
fit.  Where a later analytic estimate is still needed, the exact finite
quantity it must bound is exposed explicitly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

open ArithmeticModel StructuredCells HeadPattern

namespace PaperBridgeFit







namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]





























/-- Every integer in the guarded sample is smooth at the paper's integral
cutoff.  Guard deletion changes neither smoothness nor the head pattern. -/
theorem value_mem_smoothNumbers (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∈ Nat.smoothNumbers (yNat D.n + 1) := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.2





end StructuredSampleData



namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}



















end BaselineAllocation









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















































































/-! ### Exact main/nuisance coordinate splitting -/

































































































































/-! ## Exact target and moment correspondence -/















































































/-! ## Actual baseline mixture and coarse cells -/





























































































/-! ## Explicit finite diameter -/





















/-! ## A finite `ell^1` tilt bound -/













































/-! ## Target envelopes imply the ODE radius margin -/















/-! ## Concrete Proposition 8.7 endpoint -/











end BridgeData

/-! ## Non-circular order of asymptotic choices -/



end PaperBridgeFit

end


end Erdos390.Full

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

/- Source module: Erdos390.Full.PaperCanonicalBaseline -/
section


/-!
# Canonical barycentric baseline allocation

The active bridge first fixes positive head barycentric masses and then mixes
the two separated physical pools to hit the required logarithmic moment.
This file performs that construction exactly on the literal guarded finite
cells.  The resulting common cell-mass margin is an output.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open PaperBridgeFit ArithmeticModel

noncomputable section

variable {Head : Type*} [Fintype Head] [Nonempty Head]











namespace BarycentricTarget

variable {D : StructuredSampleData Head} (T : BarycentricTarget D)





























omit [Nonempty Head] in
/-- The two physical signs sum back to the prescribed head barycenter. -/
theorem headMarginal (h : Head) :
    ∑ sigma : PhysicalSign,
        T.baseline.normalizedCellMass (h, sigma) = T.beta h := by
  simp only [T.baseline_normalizedCellMass, cellProbability]
  rw [sum_physicalSign]
  ring

omit [Nonempty Head] in
/-- Hence every prescribed head-linear moment is exact. -/
theorem headMoment (a : Head → ℝ) :
    ∑ c : Cell Head, T.baseline.normalizedCellMass c * a c.1 =
      ∑ h : Head, T.beta h * a h := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    ∑ y : PhysicalSign, T.baseline.normalizedCellMass (h, y) * a h =
        (∑ y : PhysicalSign, T.baseline.normalizedCellMass (h, y)) * a h := by
      rw [Finset.sum_mul]
    _ = T.beta h * a h := by rw [T.headMarginal h]



end BarycentricTarget

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











end

end Erdos390.Full.GuardSquarefreeErrorRate

end

/- Source module: Erdos390.Full.PaperCanonicalHeadPhysicalTarget -/
section


/-!
# The paper's explicit head simplex and physical interpolation

The head barycenter is not supplied as an arbitrary probability vector in
the paper.  Its nonzero-vertex coefficients are exactly `A_p / (E*q)` and
the zero-vertex coefficient is the remaining mass.  This file constructs
that literal vector from the finite reserve ledger and combines it with the
two fixed physical intervals around `mu`.
-/

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit PaperHeadSimplex ArithmeticModel

noncomputable section

namespace PaperGuardCensus



namespace HeadSimplexReserve

variable {P : Finset ℕ} (R : HeadSimplexReserve P)













theorem exponent_cast_pos : 0 < (R.exponent : ℝ) := by
  exact_mod_cast R.exponent_pos



/-- The displayed barycenter has exactly the normalized target valuation at
each head prime. -/
theorem beta_exponent_moment (p : {p : ℕ // p ∈ P}) :
    ∑ h : PaperHeadSimplex.Tag P,
        R.beta h * (PaperHeadSimplex.exponent P R.exponent h p.1 : ℝ) =
      R.target p / R.activeMass := by
  rw [Fintype.sum_option]
  simp only [beta, PaperHeadSimplex.exponent_none, Nat.cast_zero,
    mul_zero, zero_add]
  rw [Finset.sum_eq_single p]
  · simp only [PaperHeadSimplex.exponent_some_self]
    field_simp [ne_of_gt R.exponent_cast_pos,
      ne_of_gt R.activeMass_pos]
  · intro q hq hqp
    have hval : p.1 ≠ q.1 := by
      intro h
      exact hqp (Subtype.ext h.symm)
    rw [PaperHeadSimplex.exponent_some_ne P R.exponent q p.1 hval]
    simp
  · intro hp
    exact (hp (Finset.mem_univ p)).elim

end HeadSimplexReserve



namespace PhysicalInterpolationTarget

variable {I : PhysicalIntervals}











end PhysicalInterpolationTarget

end PaperGuardCensus

namespace PaperBridgeFit.BridgeData

variable {P : Finset ℕ} {Band : Type*}
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData (PaperHeadSimplex.Tag P) Band)

















end PaperBridgeFit.BridgeData

end

end Erdos390.Full

end

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/











/-- Under the paper's interval-size condition, the two raw blocks exhaust
the whole lower interval `(n,2n]`. -/
theorem roughRawCandidateSet_eq_Ioc
    {n h K : ℕ} (hKh : K * h ≤ n) :
    roughRawCandidateSet n h K = Finset.Ioc n (2 * n) := by
  ext a
  simp only [roughRawCandidateSet, roughHighLowerBlock,
    roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc]
  omega

/-- The upper tail is disjoint from every raw lower candidate. -/
theorem roughUpperBlock_disjoint_rawCandidateSet
    (n h K : ℕ) :
    Disjoint (roughUpperBlock n h) (roughRawCandidateSet n h K) := by
  rw [Finset.disjoint_left]
  intro a haUpper haLower
  simp only [roughUpperBlock, roughRawCandidateSet,
    roughHighLowerBlock, roughBroadLowerBlock, Finset.mem_Ioc,
    Finset.mem_union] at haUpper haLower
  rcases haLower with haHigh | haBroad <;> omega







/-! ## The finite head and raw weights -/









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero



/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod























/-- The two physical pieces make the raw weight automatically feasible
whenever their two constant levels lie in `[0,1]`. -/
theorem roughHeadCompatibleRawWeight_mem_unitInterval
    {W n h K : ℕ} {α β L : ℝ}
    (hα : 0 ≤ α ∧ α ≤ 1)
    (hβ : 0 ≤ β / L ∧ β / L ≤ 1)
    (a : ℕ) :
    0 ≤ roughHeadCompatibleRawWeight W n h K α β L a ∧
      roughHeadCompatibleRawWeight W n h K α β L a ≤ 1 := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus W)
  · rw [roughHeadCompatibleRawWeight, if_pos hcop]
    by_cases haHigh : a ∈ roughHighLowerBlock n h K
    · have haBroad : a ∉ roughBroadLowerBlock n h K := by
        intro haBroad
        exact Finset.disjoint_left.mp
          (roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K)
          haHigh haBroad
      simpa [roughFiniteIndicator, haHigh, haBroad] using hα
    · by_cases haBroad : a ∈ roughBroadLowerBlock n h K
      · simpa [roughFiniteIndicator, haHigh, haBroad] using hβ
      · simp [roughFiniteIndicator, haHigh, haBroad]
  · simp [roughHeadCompatibleRawWeight, hcop]











/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CompleteRoughDecomposition -/
section


/-!
# Complete rough/smooth decomposition

The complete rough label retains exactly the prime-power coordinates above
`y`.  This file defines the complementary literal quotient and proves that
the two pieces recover the original natural number, with exact complementary
factorizations and no auxiliary decomposition hypothesis.
-/

namespace Erdos390.WholePaper

noncomputable section



/-! ## Positivity, divisibility, and product recovery -/

/-- A complete rough label is always positive, including for `a = 0`, when
the empty factorization gives label `1`. -/
theorem completeRoughLabel_pos (y a : ℕ) :
    0 < completeRoughLabel y a := by
  rw [completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp

theorem completeRoughLabel_ne_zero (y a : ℕ) :
    completeRoughLabel y a ≠ 0 :=
  (completeRoughLabel_pos y a).ne'

/-- Literal Finsupp form of the high-prime factorization. -/
theorem completeRoughLabel_factorization_eq_filter_gt (y a : ℕ) :
    (completeRoughLabel y a).factorization =
      a.factorization.filter (fun p ↦ y < p) := by
  simpa only [completeRoughSignature] using
    completeRoughLabel_factorization y a

/-- Coordinate form of the exact high-prime factorization. -/
theorem completeRoughLabel_factorization_apply (y a p : ℕ) :
    (completeRoughLabel y a).factorization p =
      if y < p then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeRoughLabel_factorization_eq_filter_gt y a)
  simpa only [Finsupp.filter_apply] using h

/-- The retained high-prime product is a literal divisor of the original
number. -/
theorem completeRoughLabel_dvd (y a : ℕ) :
    completeRoughLabel y a ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero _
  · rw [← Nat.factorization_le_iff_dvd
      (completeRoughLabel_ne_zero y a) ha,
      completeRoughLabel_factorization_eq_filter_gt]
    intro p
    rw [Finsupp.filter_apply]
    split_ifs <;> simp

/-- The requested multiplication direction: the original number is the
rough label times its literal complementary quotient. -/
theorem completeRough_decomposition (y a : ℕ) :
    a = completeRoughLabel y a * completeSmoothPart y a := by
  calc
    a = a / completeRoughLabel y a * completeRoughLabel y a :=
      (Nat.div_mul_cancel (completeRoughLabel_dvd y a)).symm
    _ = completeRoughLabel y a * (a / completeRoughLabel y a) :=
      Nat.mul_comm _ _
    _ = completeRoughLabel y a * completeSmoothPart y a := rfl



/-! ## The complementary low-prime factorization -/

/-- The quotient retains exactly the complementary coordinates `p ≤ y`. -/
theorem completeSmoothPart_factorization_eq_filter_le (y a : ℕ) :
    (completeSmoothPart y a).factorization =
      a.factorization.filter (fun p ↦ p ≤ y) := by
  rw [completeSmoothPart,
    Nat.factorization_div (completeRoughLabel_dvd y a),
    completeRoughLabel_factorization_eq_filter_gt]
  ext p
  simp only [Finsupp.filter_apply]
  by_cases hpLow : p ≤ y
  · have hpNotHigh : ¬y < p := Nat.not_lt_of_ge hpLow
    simp [hpLow, hpNotHigh]
  · have hpHigh : y < p := Nat.lt_of_not_ge hpLow
    simp [hpLow, hpHigh]

/-- Coordinate form of the exact low-prime factorization. -/
theorem completeSmoothPart_factorization_apply (y a p : ℕ) :
    (completeSmoothPart y a).factorization p =
      if p ≤ y then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeSmoothPart_factorization_eq_filter_le y a)
  simpa only [Finsupp.filter_apply] using h

/-- Nonzero high-part coordinates lie strictly above the cutoff. -/
theorem completeRoughLabel_factorization_support
    {y a p : ℕ}
    (hp : (completeRoughLabel y a).factorization p ≠ 0) :
    y < p := by
  rw [completeRoughLabel_factorization_apply] at hp
  by_contra hpHigh
  simp [hpHigh] at hp

/-- Nonzero smooth-part coordinates lie weakly below the cutoff. -/
theorem completeSmoothPart_factorization_support
    {y a p : ℕ}
    (hp : (completeSmoothPart y a).factorization p ≠ 0) :
    p ≤ y := by
  rw [completeSmoothPart_factorization_apply] at hp
  by_contra hpLow
  simp [hpLow] at hp

/-- Every prime divisor of the complete rough label is above `y`. -/
theorem prime_dvd_completeRoughLabel_gt
    {y a p : ℕ} (hp : p.Prime)
    (hpDvd : p ∣ completeRoughLabel y a) :
    y < p := by
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeRoughLabel_ne_zero y a) hpDvd
  exact completeRoughLabel_factorization_support hfactorPos.ne'

/-- For a positive original number, the complementary quotient is positive. -/
theorem completeSmoothPart_pos {y a : ℕ} (ha : 0 < a) :
    0 < completeSmoothPart y a := by
  rw [completeSmoothPart]
  apply Nat.div_pos
  · exact Nat.le_of_dvd ha (completeRoughLabel_dvd y a)
  · exact completeRoughLabel_pos y a

/-- For a positive original number, the complementary quotient is literally
`(y+1)`-smooth in Mathlib's positive-number convention. -/
theorem completeSmoothPart_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeSmoothPart y a ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpDvd
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeSmoothPart_pos ha).ne' hpDvd
  have hpLow : p ≤ y :=
    completeSmoothPart_factorization_support hfactorPos.ne'
  omega

/-! ## Uniqueness and the smooth-label criterion -/



/-- For positive `a`, the rough label is `1` exactly when `a` is
`(y+1)`-smooth. -/
theorem completeRoughLabel_eq_one_iff_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeRoughLabel y a = 1 ↔
      a ∈ Nat.smoothNumbers (y + 1) := by
  constructor
  · intro hlabel
    have haPart : a = completeSmoothPart y a := by
      simpa only [hlabel, one_mul] using
        completeRough_decomposition y a
    rw [haPart]
    exact completeSmoothPart_mem_smoothNumbers ha
  · intro haSmooth
    by_contra hlabel
    obtain ⟨p, hp, hpDvdLabel⟩ :=
      Nat.exists_prime_and_dvd hlabel
    have hpHigh : y < p :=
      prime_dvd_completeRoughLabel_gt hp hpDvdLabel
    have hpDvdA : p ∣ a :=
      hpDvdLabel.trans (completeRoughLabel_dvd y a)
    have hpLow :=
      (Nat.mem_smoothNumbers').mp haSmooth p hp hpDvdA
    omega



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CanonicalCompleteRoughRows -/
section


/-!
# Canonical complete rough rows for exactification

A finite candidate set itself supplies the coordinate type used by floating
rounding.  Its attained complete rough labels supply a canonical finite row
type.  The row signature is simply factorization of the label; positivity
of attained labels and uniqueness of factorization make this signature map
injective.

This file also identifies `rowSet` with the literal complete-rough fiber and
provides the value, interval, summation, and row-integrality bridges required
by the exactification interface.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Canonical finite types and maps -/



















/-! ## Signature and value interfaces -/

/-- An attained complete rough label is positive. -/
theorem canonicalCompleteRoughRow_label_pos
    (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    0 < row.1 := by
  obtain ⟨a, _ha, hlabel⟩ :=
    mem_completeRoughLabelSet.mp row.property
  rw [← hlabel, completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp









/-! ## Literal subtype fibers and `rowSet` -/











/-! ## Summation and integrality bridges -/











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasCanonicalRowBridge -/
section


/-!
# Canonical-row consumer for the weighted Saias block

The analytic four-endpoint expression is useful to the construction only
after it is tied back to the literal complete-rough row used by floating
rounding.  This file supplies that consumer-facing bridge.  The sum over a
canonical `rowSet` is identified unconditionally with the already-defined
literal raw row mass.  The upper quota minus that mass is then connected to
`roughPhysicalFriableCombination` and hence to the weighted Saias bound.

The upper endpoint identification is an exact equality.  Finite head
inclusion--exclusion and the fixed-head physical shift occur between the
literal raw mass and the density-scaled four-endpoint block in the paper,
so their error is retained as a separate explicit allowance.  It is not
silently folded into the HT--Saias hypothesis.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section







/-- Every attained canonical row label has the intrinsic complete-rough
support property. -/
theorem isCompleteRoughLabel_of_canonicalCompleteRoughRow
    {y : ℕ} {A : Finset ℕ}
    (row : CanonicalCompleteRoughRow y A) :
    IsCompleteRoughLabel y row.1 := by
  constructor
  · exact canonicalCompleteRoughRow_label_pos y A row
  · obtain ⟨a, _ha, hlabel⟩ := mem_completeRoughLabelSet.mp row.2
    intro p hp
    rw [← hlabel] at hp
    exact completeRoughLabel_factorization_support hp









































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRoughRowCorrection -/
section


/-!
# Finite constant-pool correction of one canonical rough row

The Saias-facing quantity `roughCanonicalRawRowQuotaError` is a row-mass
error.  The paper corrects such an error by spreading it uniformly over a
nonempty clean broad subpool in the same complete-signature row.  This file
formalizes that finite operation directly.

No selector handoff, feasibility conclusion, prime-residual estimate, or
asymptotic pool lower bound is assumed.  Exact row mass is an algebraic
consequence of nonemptiness and containment of the correction pool.
Feasibility is then *derived* from two explicit numerical facts: the raw
coordinates have a stated two-sided margin and the constant correction
density is no larger than that margin.

The final specialization uses the literal upper-row cardinality as target,
the literal head-compatible raw weight as baseline, and the head-free broad
fiber as correction pool.  Establishing the paper's uniform lower bound for
that pool after all guards, and the corresponding `o(1 / log n)` density
bound, remains a separate arithmetic task.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Generic finite constant-pool correction -/









/-- Spreading the row error over a nonempty subpool makes the row sum
exactly equal to the requested target. -/
theorem sum_bankPaperConstantPoolCorrection_eq_target
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target : ℝ}
    (hpool : pool ⊆ row) (hpoolNonempty : pool.Nonempty) :
    ∑ a ∈ row, bankPaperConstantPoolCorrection row pool x target a =
      target := by
  have hfilter : row.filter (fun a ↦ a ∈ pool) = pool := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact fun ha ↦ ha.2
    · exact fun ha ↦ ⟨hpool ha, ha⟩
  have hcardNat : pool.card ≠ 0 :=
    Finset.card_ne_zero.mpr hpoolNonempty
  have hcardReal : (pool.card : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  have hcorrectionSum :
      (∑ a ∈ row,
        if a ∈ pool then
          bankPaperConstantPoolCorrectionDensity row pool x target
        else 0) =
        (pool.card : ℝ) *
          bankPaperConstantPoolCorrectionDensity row pool x target := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hcancel :
      (pool.card : ℝ) *
          ((target - ∑ a ∈ row, x a) / (pool.card : ℝ)) =
        target - ∑ a ∈ row, x a := by
    rw [mul_comm, div_mul_cancel₀ _ hcardReal]
  calc
    ∑ a ∈ row, bankPaperConstantPoolCorrection row pool x target a =
        (∑ a ∈ row, x a) +
          ∑ a ∈ row,
            if a ∈ pool then
              bankPaperConstantPoolCorrectionDensity row pool x target
            else 0 := by
      simp only [bankPaperConstantPoolCorrection]
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ row, x a) +
        (pool.card : ℝ) *
          bankPaperConstantPoolCorrectionDensity row pool x target := by
      rw [hcorrectionSum]
    _ = (∑ a ∈ row, x a) +
        (pool.card : ℝ) *
          ((target - ∑ a ∈ row, x a) / (pool.card : ℝ)) := by
      rw [bankPaperConstantPoolCorrectionDensity]
    _ = target := by
      rw [hcancel]
      ring





/-! ## Literal canonical rough-row specialization -/

















/-! ## Assembly over all attained complete rough rows -/













/-! ## Unconditional capped-quota selector -/





















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomMarkerPools -/
section


/-!
# Literal marker pools for the four bottom bank moves

The four rows below are the natural-number half-open intervals appearing in
the paper.  Each is split at its integer midpoint into two fixed one-half
orientation subintervals.  This file proves only exact finite interval and
factor arithmetic; prime supply is deliberately kept separate.
-/

namespace Erdos390.WholePaper

noncomputable section











































/-- A marker in its row makes both endpoint states and the donor lie in
the factor interval `(n,M]`. -/
theorem bankBottom_states_donor_mem_factorInterval
    {n M marker : ℕ} {move : BankBottomMove}
    (hmarker : marker ∈ bankBottomMarkerInterval n M move) :
    bankBottomLowerState move marker ∈ factorInterval n M ∧
      bankBottomUpperState move marker ∈ factorInterval n M ∧
      bankBottomDonor move marker ∈ factorInterval n M := by
  cases move <;>
    simp only [bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, bankBottomLowerState,
      bankBottomUpperState, bankBottomDonor,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier, factorInterval] at hmarker ⊢ <;>
    omega



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomPaperComponents -/
section


/-!
# Actual bottom-bank components from the concrete marker matching

The capacity argument deliberately matches the rectangular upper-bound family
consisting of every signed slot and all four bottom rows.  The path belonging
to a small source prime does not use every one of those rows: source `3` uses
only `3→2→1`, and source `2` uses only `2→1`.  This file therefore separates
the full matched family from the literal relevant subfamily before forming any
set of used occurrences.

For every matched request we retain its actual prime marker, the two state
factors in the corresponding row, and its donor occurrence.  A finite set of
occurrence values is used, so in the last two rows the donor and the upper
state are literally one occurrence, rather than two tagged copies.  The only
global input is the already constructed injective marker matching.  All other
claims below are explicit interval, factorization, and large-prime arithmetic.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal relevant subfamily -/





















































/-! ## The deterministic truncated bottom path -/

























/-! ## A realization obtained from the actual matching -/





namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)





















/-- Both row endpoints and the donor are actual factors in `(n,M]`. -/
theorem states_donor_mem_factorInterval (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.lowerStateFactor request ∈ factorInterval n M ∧
      realization.upperStateFactor request ∈ factorInterval n M ∧
      realization.donorFactor request ∈ factorInterval n M := by
  simpa only [lowerStateFactor, upperStateFactor, donorFactor] using
    bankBottom_states_donor_mem_factorInterval
      (realization.marker_mem_row hTwoN request)







/-! The four paper rows, with the marker made explicit. -/













/-! ## Orientation-aware realized row and slot changes -/























end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/









namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)























































end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)









/-! ## Relevant markers and marker-to-component uniqueness -/



























end BankBottomPaperRealization

/-! ## Cardinality bound for the actual relevant marker set -/







/-! ## Eventual local geometry and the terminal realized family -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryPaperComponents -/
section


/-!
# Realized ordinary bank components

An ordinary matching supplies an actual pair `(P,u)` to every concrete path
request `q→b`.  This file materializes the three factor occurrences

* source state `P*q`,
* target state `P*b`, and
* backing donor `P*u`.

All three lie in `(n,M]` and have the same complete rough signature.  The
large prime marker is recovered uniquely from any realized occurrence, which
gives marker injectivity, donor-product injectivity, and collision-freedom
across requests, scales, and orientations.  Finally, cancellation of the
common marker turns the realized component changes back into the actual
finite path telescope.

The public names intentionally mirror `BankBottomPaperComponents`: a
realization object, factor-valued methods, an occurrence-kind enumeration,
and `occurrenceValue`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Coarse global size bounds -/













/-! ## Arithmetic helpers for rough signatures -/









/-! ## Marker injectivity inherited from the orientation pools -/









/-! ## The public realization object and its actual factors -/



namespace BankOrdinaryPaperRealization





































theorem donorValue_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.donorValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  simp only [donorValue, factorInterval, Finset.mem_Ioc]
  have hlower := heligible.2.2.2.2.2.2.1
  change 2 * n < R.marker request * R.donorCore request at hlower
  exact ⟨by omega, heligible.2.2.2.2.2.2.2⟩





































/-! ## The three actual occurrences and global collision-freedom -/





theorem two_mul_n_lt_donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    2 * n < R.donorValue request :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.2.2.2.2.1

































/-! ## Realized component and signed-slot changes -/























end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperComponents -/
section


/-!
# Combined bottom and ordinary bank realization

This file is only the composition layer.  The two allocation mechanisms stay
independent, but their marker ranges are strictly separated:

`3 * ordinaryMarker < n < 3 * bottomMarker`.

Consequently the marker maps remain injective after the two request families
are joined.  Prime-marker recovery also turns this strict separation into
cross-family disjointness of the actual state/donor occurrence sets.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section





namespace BankPaperRealization





/-- Marker assignment is globally injective after adjoining the relevant
bottom requests and all ordinary requests. -/
theorem marker_injective
    {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.marker := by
  intro request request' hmarker
  cases request with
  | inl bottomRequest =>
      cases request' with
      | inl bottomRequest' =>
          have hrequest : bottomRequest = bottomRequest' :=
            R.bottom.relevantMarkerMap_injective
              (by simpa only [marker] using hmarker)
          exact congrArg Sum.inl hrequest
      | inr ordinaryRequest =>
          exfalso
          have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
          simp only [marker] at hmarker
          omega
  | inr ordinaryRequest =>
      cases request' with
      | inl bottomRequest =>
          exfalso
          have hlt := R.ordinaryMarker_lt_bottomMarker ordinaryRequest
            (bankBottomRelevantRequestToPaperRequest bottomRequest)
          simp only [marker] at hmarker
          omega
      | inr ordinaryRequest' =>
          have hrequest : ordinaryRequest = ordinaryRequest' :=
            R.ordinary.marker_injective
              (by simpa only [marker] using hmarker)
          exact congrArg Sum.inr hrequest











/-! ## Cross-family actual occurrence disjointness -/

















end BankPaperRealization

/-! ## Terminal combined realization -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorCutoff -/
section


/-!
# The fixed-prefix central-anchor cutoff

For a fixed prefix depth `R`, the paper splits the central prime blocks at
`n / (R + 1)`.  This file gives an explicit sufficient threshold for all
scale separations and then connects that literal cutoff directly to the
large-prime routing and central-anchor product APIs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







/-- At the explicit threshold, the cutoff is at least `4(R+1)`. -/
theorem four_mul_succ_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    4 * (R + 1) ≤ centralAnchorCutoff R n := by
  rw [centralAnchorCutoff, Nat.le_div_iff_mul_le (by omega)]
  simpa only [centralAnchorCutoffThreshold, pow_two, mul_assoc] using hn



/-- The explicit threshold also puts `2n` strictly below the cutoff square. -/
theorem two_mul_lt_centralAnchorCutoff_sq
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * n < (centralAnchorCutoff R n) ^ 2 := by
  let X := centralAnchorCutoff R n
  have hX : 4 * (R + 1) ≤ X := by
    simpa only [X] using four_mul_succ_le_centralAnchorCutoff hn
  have hXPos : 0 < X := by omega
  have hnUpper : n < (R + 1) * (X + 1) := by
    simpa only [X, centralAnchorCutoff] using
      Nat.lt_mul_div_succ n (by omega : 0 < R + 1)
  have hlinear : 2 * (R + 1) * (X + 1) ≤ X ^ 2 := by
    calc
      2 * (R + 1) * (X + 1) ≤ 2 * (R + 1) * (2 * X) := by
        exact Nat.mul_le_mul_left (2 * (R + 1)) (by omega)
      _ = (4 * (R + 1)) * X := by ring
      _ ≤ X * X := Nat.mul_le_mul_right X hX
      _ = X ^ 2 := by ring
  calc
    2 * n < 2 * ((R + 1) * (X + 1)) :=
      (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
    _ = 2 * (R + 1) * (X + 1) := by ring
    _ ≤ X ^ 2 := hlinear







































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrecharge -/
section


/-!
# The actual precharged bank state

This module is independent of the eventual path selector.  Its component
index is the already realized global request type: every relevant bottom row
and every ordinary row occurs exactly once.  For each component we expose its
orientation-aware base and alternate states and its actual donor occurrence.

The proofs below use only the explicit component geometry.  In particular,
there is no abstract capacity or compatibility hypothesis: global
injectivity follows from the realized occurrence-set disjointness, and the
donor tail is the literal interval `(2n,M]`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section



namespace BankBottomPaperRealization

/-- Every actual bottom donor is in the strict tail above `2n`. -/
theorem two_mul_n_lt_donorFactor
    {n M : ℕ} (R : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    2 * n < R.donorFactor request := by
  have hrow := R.marker_mem_row hTwoN request
  cases hmove : R.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, donorFactor,
      bankBottomDonor, bankBottomDonorMultiplier] at hrow ⊢ <;> omega

end BankBottomPaperRealization

namespace BankPaperRealization

attribute [local instance] Erdos390.WholePaper.BankPaperRealization.bankPaperMarkerRequestDecidableEq

/-! ## Global component data -/

























/-! ## Complete rough signatures -/







/-! ## Endpoint and donor injectivity -/





















/-! ## Literal finite states, donor tail, and replacement map -/

























/-- Every donor, ordinary or bottom, is an actual factor in `(2n,M]`. -/
theorem prechargeDonorValue_mem_tail
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ Finset.Ioc (2 * n) M := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      have hlower := R.bottom.two_mul_n_lt_donorFactor
        R.ordinary.two_mul_n_le_M fullRequest
      have hupper : R.bottom.donorFactor fullRequest ≤ M := by
        have hdata : n < R.bottom.donorFactor fullRequest ∧
            R.bottom.donorFactor fullRequest ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.bottom.states_donor_mem_factorInterval
              R.ordinary.two_mul_n_le_M fullRequest).2.2
        exact hdata.2
      simpa only [prechargeDonorValue, fullRequest,
        Finset.mem_Ioc] using And.intro hlower hupper
  | inr request =>
      have hlower := R.ordinary.two_mul_n_lt_donorValue request
      have hupper : R.ordinary.donorValue request ≤ M := by
        have hdata : n < R.ordinary.donorValue request ∧
            R.ordinary.donorValue request ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.ordinary.donorValue_mem_factorInterval request)
        exact hdata.2
      simpa only [prechargeDonorValue, Finset.mem_Ioc] using
        And.intro hlower hupper

theorem prechargeDonorSet_subset_tail
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet ⊆ Finset.Ioc (2 * n) M := by
  intro donor hdonor
  rw [prechargeDonorSet, indexedPathState, Finset.mem_image] at hdonor
  obtain ⟨request, _hrequest, rfl⟩ := hdonor
  exact R.prechargeDonorValue_mem_tail request





















/-! ## Component counts and the base product -/























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalBacking -/
section


/-!
# The literal fixed exceptional factors and their high-prime backing

The paper fixes every upper-tail factor whose complete rough row has real
scale `2n / R_y(a) < n ^ deltaStar`, except for the actual donor occurrences
already withheld for the precharged bank.  This file makes that set literal.

The definition deliberately uses the displayed real quotient and real power.
It is not the larger integral test obtained by flooring the rough scale and
ceiling the exceptional cutoff.

At every prime above the rough cutoff, replacing the donor set by the bank's
base state preserves factorization coordinatewise.  The fixed exceptional
factors and donors are disjoint subsets of the literal tail, so their union
is an unconditional backing product for the complete selector charge in
all such coordinates.  No small-prime charge estimate is asserted here.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section







namespace BankPaperRealization





theorem paperFixedExceptionalFactors_subset_upperBlock
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆ roughUpperBlock n h := by
  intro a ha
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
  exact (mem_paperExceptionalUpperFactors.mp ha.1).1





















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger -/
section


/-!
# Guard-local canonical rough-row ledger

This module isolates the finite bookkeeping that occurs when the paper
passes from the raw canonical rough candidates to the candidates left after
the numerical guards

`Gamma_num = anchors ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Only literal finite-set identities are proved here.  In particular, this
file does **not** assume or assert a local guard census, a lower bound for a
guarded broad pool, or enough guarded-row capacity for a corrected selector.
Those still-missing estimates are exposed at the end as named propositions.

The postcharge target is kept in `Real` form for the correction algebra and
in `Int` form for its exact integrality witness.  Its nonnegativity is a
finite consequence of the actual donor/base row-preserving bijection and of
the disjoint upper-tail backing of the fixed exceptional factors and donors.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Literal guarded candidates and row pieces -/













theorem roughCanonicalGuardedCandidateSet_disjoint_guardSet
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K : ℕ) :
    Disjoint
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (R.roughCanonicalGuardSet certificate deltaStar) := by
  exact Finset.sdiff_disjoint













/-! ## The donor/base row-preserving bijection -/









/-! ## Upper-tail ownership and the postcharge target -/





/-- Every non-smooth row is either active nonexceptional or exceptional.
No asymptotic hypothesis is needed for this literal order dichotomy. -/
theorem roughCanonical_activeNonexceptional_or_exceptional
    {n label : ℕ} {deltaStar : ℝ} (hlabel : label ≠ 1) :
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ∨
      RoughCanonicalExceptionalLabel n deltaStar label := by
  by_cases hactive :
      (n : ℝ) ^ deltaStar ≤ 2 * (n : ℝ) / (label : ℝ)
  · exact Or.inl ⟨hlabel, hactive⟩
  · exact Or.inr (lt_of_not_ge hactive)























/-! ## Exact local discrepancy ledger -/







/-! ## Exact support reduction for the local deletion set -/

/-- Fixed exceptional factors cannot themselves be raw lower candidates. -/
theorem roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (roughRawCandidateSet n h K)
      (R.paperFixedExceptionalFactors deltaStar) := by
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) (R.paperFixedExceptionalFactors_subset_upperBlock deltaStar)

/-- Actual donors also lie strictly above every raw lower candidate. -/
theorem roughRawCandidateSet_disjoint_prechargeDonorSet
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    Disjoint (roughRawCandidateSet n h K) R.prechargeDonorSet := by
  have hdonor : R.prechargeDonorSet ⊆ roughUpperBlock n h := by
    simpa only [roughUpperBlock, upperEndpoint] using
      R.prechargeDonorSet_subset_tail
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) hdonor

/-- Consequently, the only guard families which can delete a raw lower
coordinate are anchors and the two bank endpoint states.  This is a support
statement, not the still-missing per-row cardinality census. -/
theorem roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState := by
  intro a ha
  have haData := Finset.mem_inter.mp ha
  have haRaw := (mem_completeRoughRowFiber.mp haData.1).1
  have haGuard := haData.2
  simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
    Finset.mem_union] at haGuard
  simp only [Finset.mem_union]
  rcases haGuard with (((haAnchor | haFixed) | haDonor) | haBase) | haAlt
  · exact Or.inl (Or.inl haAnchor)
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
        deltaStar)) haRaw haFixed).elim
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_prechargeDonorSet
        (K := K))) haRaw haDonor).elim
  · exact Or.inl (Or.inr haBase)
  · exact Or.inr haAlt

/-! ## Explicit remaining finite/analytic obligations -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardCapacityReduction -/
section


/-!
# Canonical rough-row guard capacity reduction

This file closes the finite part of the three guard-local obligations exposed
by `BankPaperCanonicalGuardLocalRowLedger`.

For every non-smooth complete rough row, at most one central anchor, one bank
base, and one bank alternate can occur.  Thus the literal local guard census
is at most three.  Removing those three possible coordinates from a raw broad
pool gives the guarded-pool capacity, and containment of the guarded broad
pool in the guarded row gives the postcharge capacity.

The only non-finite input left visible is `RoughCanonicalActiveRawBroadSurplus`:
the raw broad pool must contain the larger of the requested pool minimum and
the literal upper-row target, plus the three-coordinate guard slack.  This is
the exact de Bruijn--Saias lower-bound consequence still needed from the
analytic rough-row argument; it contains no selector or bookkeeping premise.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Complete rough labels remember retained prime divisors -/

/-- A prime divisor above the smooth cutoff is retained in the complete
rough label. -/
theorem prime_dvd_completeRoughLabel_of_cutoff_lt
    {y a p : Nat} (hp : p.Prime) (hyp : y < p)
    (ha : a ≠ 0) (hpa : p ∣ a) :
    p ∣ completeRoughLabel y a := by
  apply (hp.dvd_iff_one_le_factorization
    (completeRoughLabel_ne_zero y a)).mpr
  rw [completeRoughLabel_factorization_apply, if_pos hyp]
  exact (hp.dvd_iff_one_le_factorization ha).mp hpa



/-! ## One central anchor in every non-smooth row -/



/-- Consequently, one fixed non-smooth rough row meets the guarded central
anchor set in at most one coordinate. -/
theorem completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
    {c : Real} {depth n y : Nat} {left right : Nat -> Nat}
    {changed candidates : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyTwo : 2 <= y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (label : Nat) (hlabel : label ≠ 1) :
    (completeRoughRowFiber y candidates label ∩
      certificate.anchors).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haData := Finset.mem_inter.mp ha
  have hbData := Finset.mem_inter.mp hb
  have haLabel := (mem_completeRoughRowFiber.mp haData.1).2
  have hbLabel := (mem_completeRoughRowFiber.mp hbData.1).2
  apply fullCentralAnchors_completeRoughLabel_injective_of_ne_one
    hnCutoff hyTwo hyCutoff certificate.isCofactorChoice
  · simpa only [certificate.anchors_eq] using haData.2
  · simpa only [certificate.anchors_eq] using hbData.2
  · simpa only [haLabel] using hlabel
  · rw [haLabel, hbLabel]

namespace BankPaperRealization

/-! ## One base and one alternate in every bank row -/

/-- The global bank marker is prime. -/
theorem paperMarker_prime
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    (R.marker request).Prime := by
  cases request with
  | inl request =>
      exact R.bottom.marker_prime
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.marker_prime request

/-- Every global bank marker lies above the complete rough cutoff. -/
theorem yNat_lt_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    yNat n < R.marker request := by
  cases request with
  | inl request =>
      exact R.bottom.yNat_lt_marker R.ordinary.two_mul_n_le_M
        R.three_mul_yNat_le_n
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.yNat_lt_marker request

/-- The actual donor has the same complete rough signature as its global
marker. -/
theorem prechargeDonor_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n) (R.prechargeDonorValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      simpa only [prechargeDonorValue, marker, fullRequest,
        BankBottomPaperRealization.occurrenceValue_donor] using
        (R.bottom.occurrenceValue_completeRoughSignature R.six_le_yNat
          fullRequest .donor)
  | inr request =>
      have hsignature := completeRoughSignature_marker_mul_smooth_eq
        (y := yNat n) (P := R.ordinary.marker request)
        (a := R.ordinary.donorCore request) (b := 1)
        (R.ordinary.marker_prime request).ne_zero
        (R.ordinary.donorCore_smooth request)
        (by simp [Nat.mem_smoothNumbers])
      simpa only [prechargeDonorValue, marker,
        BankOrdinaryPaperRealization.donorValue, mul_one] using hsignature

theorem prechargeBase_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.prechargeBase_donor_completeRoughSignature_eq request).trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

theorem prechargeAlternate_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.precharge_completeRoughSignature_eq request).2.trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

/-- A prime above the cutoff is its own complete rough label. -/
theorem completeRoughLabel_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.marker request) = R.marker request := by
  have hprime := R.paperMarker_prime request
  have hhigh := R.yNat_lt_paperMarker request
  apply Nat.dvd_antisymm
  · exact completeRoughLabel_dvd (yNat n) (R.marker request)
  · exact prime_dvd_completeRoughLabel_of_cutoff_lt hprime hhigh
      hprime.ne_zero (dvd_refl (R.marker request))

theorem prechargeBase_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      R.marker request := by
  calc
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeBase_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request

theorem prechargeAlternate_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) = R.marker request := by
  calc
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeAlternate_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request

theorem prechargeBase_completeRoughLabel_injective
    {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n) (R.prechargeBaseStateValue request)) := by
  intro request request' heq
  apply R.marker_injective
  change
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      completeRoughLabel (yNat n)
        (R.prechargeBaseStateValue request') at heq
  simpa only [R.prechargeBase_completeRoughLabel_eq_marker] using heq

theorem prechargeAlternate_completeRoughLabel_injective
    {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request)) := by
  intro request request' heq
  apply R.marker_injective
  change
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request') at heq
  simpa only [R.prechargeAlternate_completeRoughLabel_eq_marker] using heq

private theorem completeRoughRowFiber_inter_indexedPathState_card_le_one
    {C : Type*} [Fintype C] [DecidableEq C]
    {y label : Nat} {candidates : Finset Nat} (state : C -> Nat)
    (hinjective : Function.Injective
      (fun component => completeRoughLabel y (state component))) :
    (completeRoughRowFiber y candidates label ∩
      indexedPathState state).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haData := Finset.mem_inter.mp ha
  have hbData := Finset.mem_inter.mp hb
  have haLabel := (mem_completeRoughRowFiber.mp haData.1).2
  have hbLabel := (mem_completeRoughRowFiber.mp hbData.1).2
  rw [indexedPathState, Finset.mem_image] at haData hbData
  obtain ⟨component, _hcomponent, rfl⟩ := haData.2
  obtain ⟨component', _hcomponent', rfl⟩ := hbData.2
  apply congrArg state
  apply hinjective
  change completeRoughLabel y (state component) =
    completeRoughLabel y (state component')
  rw [haLabel, hbLabel]

theorem completeRoughRowFiber_inter_prechargeBaseState_card_le_one
    {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeBaseState).card <= 1 := by
  classical
  rw [prechargeBaseState]
  exact completeRoughRowFiber_inter_indexedPathState_card_le_one
    R.prechargeBaseStateValue
    R.prechargeBase_completeRoughLabel_injective

theorem completeRoughRowFiber_inter_prechargeAlternateState_card_le_one
    {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeAlternateState).card <= 1 := by
  classical
  rw [prechargeAlternateState]
  exact completeRoughRowFiber_inter_indexedPathState_card_le_one
    R.prechargeAlternateStateValue
    R.prechargeAlternate_completeRoughLabel_injective

/-! ## The literal three-coordinate local census -/

/-- In every non-smooth complete rough row, the numerical guards delete at
most one anchor, one bank base, and one bank alternate.  Fixed exceptional
factors and donors are in the upper tail and were already removed by the
support theorem in the local ledger. -/
theorem roughCanonicalGuardLocalCensusBound_three_of_ne_one
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hlabel : label ≠ 1) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label 3 := by
  let rawRow := completeRoughRowFiber (yNat n)
    (roughRawCandidateSet n h K) label
  have hsubset :
      R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
        (rawRow ∩ certificate.anchors) ∪
          (rawRow ∩ R.prechargeBaseState) ∪
            (rawRow ∩ R.prechargeAlternateState) := by
    intro a ha
    have haDeleted := ha
    change a ∈ rawRow ∩
      R.roughCanonicalGuardSet certificate deltaStar at haDeleted
    have haRaw : a ∈ rawRow := by
      exact (Finset.mem_inter.mp haDeleted).1
    have haSupport :=
      R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
        certificate deltaStar K label ha
    rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
    · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_inter.mpr ⟨haRaw, haAnchor⟩
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_inter.mpr ⟨haRaw, haBase⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_inter.mpr ⟨haRaw, haAlternate⟩
  have hanchor : (rawRow ∩ certificate.anchors).card <= 1 := by
    have hyTwo : 2 <= yNat n := by
      have hySix := R.six_le_yNat
      omega
    exact completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
      certificate hnCutoff hyTwo hyCutoff label hlabel
  have hbase : (rawRow ∩ R.prechargeBaseState).card <= 1 := by
    exact R.completeRoughRowFiber_inter_prechargeBaseState_card_le_one
      (roughRawCandidateSet n h K)
  have halternate :
      (rawRow ∩ R.prechargeAlternateState).card <= 1 := by
    exact R.completeRoughRowFiber_inter_prechargeAlternateState_card_le_one
      (roughRawCandidateSet n h K)
  have hfirst := Finset.card_union_le
    (rawRow ∩ certificate.anchors) (rawRow ∩ R.prechargeBaseState)
  have hall := Finset.card_union_le
    ((rawRow ∩ certificate.anchors) ∪
      (rawRow ∩ R.prechargeBaseState))
    (rawRow ∩ R.prechargeAlternateState)
  have hcard := Finset.card_le_card hsubset
  exact show
    (R.roughCanonicalGuardDeletedRow certificate deltaStar K label).card <= 3
    by omega

/-- Active nonexceptional rows are non-smooth, so the preceding census
directly supplies the first Section 9 guard-local input. -/
theorem roughCanonicalGuardLocalCensusBound_three_of_active
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label 3 :=
  R.roughCanonicalGuardLocalCensusBound_three_of_ne_one certificate
    deltaStar K label hnCutoff hyCutoff hactive.1

/-! ## Guarded broad-pool and postcharge capacities -/

/-- A raw pool with `budget` units of surplus retains its requested minimum
after deleting a guard whose intersection with the row has that census. -/
theorem roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K label minimum budget : Nat)
    (hcensus : RoughCanonicalGuardLocalCensusBound R certificate deltaStar
      K label budget)
    (hraw : minimum + budget <=
      (roughCanonicalBroadCorrectionPool W n h K (yNat n) label).card) :
    RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar W K
      label minimum := by
  have hinterSubset :
      roughCanonicalBroadCorrectionPool W n h K (yNat n) label ∩
          R.roughCanonicalGuardSet certificate deltaStar ⊆
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label := by
    intro a ha
    have haData := Finset.mem_inter.mp ha
    exact Finset.mem_inter.mpr
      ⟨roughCanonicalBroadCorrectionPool_subset_rawRow
        W n h K (yNat n) label haData.1, haData.2⟩
  have hinter :
      (roughCanonicalBroadCorrectionPool W n h K (yNat n) label ∩
        R.roughCanonicalGuardSet certificate deltaStar).card <= budget :=
    (Finset.card_le_card hinterSubset).trans hcensus
  unfold RoughCanonicalGuardedBroadPoolCapacity
  rw [roughCanonicalGuardedBroadCorrectionPool, Finset.card_sdiff,
    Finset.inter_comm]
  omega

/-- The postcharge target never exceeds the uncorrected upper-row target. -/
theorem roughCanonicalPostchargeRowTarget_le_upperTarget
    {n h : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) (label : Nat) :
    R.roughCanonicalPostchargeRowTarget deltaStar label <=
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) := by
  have hfixed : 0 <=
      (completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) label : Real) := by
    positivity
  have hbase : 0 <=
      (completeLabelMultiplicity (yNat n)
        R.prechargeBaseState label : Real) := by
    positivity
  unfold roughCanonicalPostchargeRowTarget
  linarith

/-- Any guarded broad-pool lower bound at least as large as the literal
upper-row target supplies capacity for the nonnegative postcharge quota. -/
theorem roughCanonicalPostchargeRowCapacity_of_guardedBroadPoolCapacity
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K label minimum : Nat)
    (hupper : roughUpperCompleteRoughRowTarget n h (yNat n) label <= minimum)
    (hpool : RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
      W K label minimum) :
    RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label := by
  have htarget := R.roughCanonicalPostchargeRowTarget_le_upperTarget
    deltaStar label
  have hupperReal :
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) <=
        (minimum : Real) := by
    exact_mod_cast hupper
  have hpoolRow := Finset.card_le_card
    (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar W K label)
  have hminimumPool : minimum <=
      (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card := hpool
  unfold RoughCanonicalPostchargeRowCapacity
  exact htarget.trans <| hupperReal.trans <| by
    exact_mod_cast hminimumPool.trans hpoolRow

/-! ## The single remaining analytic raw-pool input -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic -/
section


/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/







/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/













/-! ## Uniform paper-scale choices -/



















/-- The intrinsic surplus and the literal three-coordinate guard census give
guarded-row capacity before candidate-label attainment is known.  This is
the noncircular coverage input needed when all upper rows are summed. -/
theorem BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
    (W K poolMinimum : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat) (left right : Nat -> Nat)
        (changed : Finset Nat),
      forall (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
      forall label, IsCompleteRoughLabel (yNat n) label ->
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalGuardLocalCensusBound R certificate deltaStar K
              label 3 ∧
            RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
              W K label poolMinimum ∧
            RoughCanonicalPostchargeRowCapacity R certificate deltaStar K
              label := by
  filter_upwards [eventually_roughCanonicalActiveIntrinsicRawBroadSurplus
    W K poolMinimum hc hdelta] with n hsurplus
  intro depth left right changed R certificate hnCutoff hyCutoff
    label hlabel hactive
  have hcensus : RoughCanonicalGuardLocalCensusBound R certificate
      deltaStar K label 3 :=
    R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
      deltaStar K label hnCutoff hyCutoff hactive
  have hbroad : RoughCanonicalGuardedBroadPoolCapacity R certificate
      deltaStar W K label poolMinimum := by
    apply R.roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus certificate
      deltaStar W K label poolMinimum 3 hcensus
    exact le_trans
      (Nat.add_le_add_right (Nat.le_max_left _ _) 3)
      (hsurplus label hlabel hactive)
  have hpostcharge : RoughCanonicalPostchargeRowCapacity R certificate
      deltaStar K label := by
    let minimum := max poolMinimum
      (roughUpperCompleteRoughRowTarget n (upperTailLength c n)
        (yNat n) label)
    have hcapacity : RoughCanonicalGuardedBroadPoolCapacity R certificate
        deltaStar W K label minimum := by
      apply R.roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus
        certificate deltaStar W K label minimum 3 hcensus
      exact hsurplus label hlabel hactive
    apply R.roughCanonicalPostchargeRowCapacity_of_guardedBroadPoolCapacity
      certificate deltaStar W K label minimum
    · exact Nat.le_max_right _ _
    · exact hcapacity
  exact ⟨hcensus, hbroad, hpostcharge⟩



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankAnchorCollisionFree -/
section


/-!
# Collision freedom between the complete central anchors and the actual bank

The large-anchor branch recovers the common prime marker from the complete
rough factorization above `yNat`.  Once the marker is recovered, the guarded
central-cofactor certificate excludes the two incident state cores.

The residual branch uses the more rigid shape
`2^k * p^e`.  A bottom marker is already above the residual cutoff.  For an
ordinary marker, divisibility first forces the residual base prime to be the
marker; its marker valuation is then one, so cancellation would make the
ordinary state core a power of two, contrary to the path certificate.

Donor-only occurrences do not create an extra case: ordinary donors and the
two nonterminal bottom donors lie above `2n`, while terminal bottom donors
are literally their upper endpoint state.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The two eventual scale separations used by marker recovery -/

/-- The elementary square bound behind the separation
`yNat n < centralAnchorCutoff depth n`. -/
theorem bankAnchor_yNat_mul_self_le_self
    {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [Erdos390.Full.Scale.y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast





/-- At the literal central-anchor threshold, the moving smooth cutoff is
strictly below the residual/large-prime cutoff. -/
theorem yNat_lt_centralAnchorCutoff_of_threshold
    {depth n : ℕ} (hn : 1 ≤ n)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    yNat n < centralAnchorCutoff depth n := by
  have hySq := bankAnchor_yNat_mul_self_le_self hn
  have hcutSq := two_mul_lt_centralAnchorCutoff_sq hnCutoff
  nlinarith

theorem eventually_yNat_lt_centralAnchorCutoff (depth : ℕ) :
    ∀ᶠ n : ℕ in atTop, yNat n < centralAnchorCutoff depth n := by
  filter_upwards [eventually_ge_atTop 1,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth)]
      with n hn hnCutoff
  exact yNat_lt_centralAnchorCutoff_of_threshold hn hnCutoff

/-! ## Arithmetic collision kernels -/



namespace BankPaperRealization



/-! ## Literal recovery of the incident cores from actual requests -/





















/-! ## Complete finite collision theorem -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardedBridgeConnector -/
section


/-!
# Canonical guarded selector to bridge-fit connector

This module joins the finite objects on the two sides of the Section 8/9
interface without asserting the missing selector theorem.

* `bankPaperCanonicalBridgeData` builds the literal `PaperBridgeFit.BridgeData`
  from an existing guarded structured sample, the canonical barycentric
  baseline, and the canonical regular-mesh partition.
* `BankPaperCanonicalGuardedBridgeSelectorConstructor` is the sole
  existential socket.  Its witness is an actual guarded selector satisfying
  the already defined rounded-selector tangent input and agreeing with the
  bridge baseline on the active structured sample.
* the projection and frozen-layer theorems derive the smooth integer quota,
  feasibility, row integrality, prime-band balance and support, tangent
  balance and pointwise/prefix bounds, the frozen feasibility ledger, and the
  total integer quota.  No one of those conclusions is repeated as a new
  premise.

The active structured sample need only be a subset of the guarded smooth row;
it is not silently identified with the whole row.  All other guarded
coordinates are retained in the frozen layer with their selector weights,
while the fixed exceptional factors have weight one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open BankPaperRealization

noncomputable section

/-! ## Canonical bridge data -/















/-! ## Active values and integer row quotas -/



theorem mem_bankPaperCanonicalBridgeActiveValues
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData Head Band} {a : Nat} :
    a ∈ bankPaperCanonicalBridgeActiveValues B ↔
      ∃ m : B.sampleData.Sample, B.sampleData.value m = a := by
  simp [bankPaperCanonicalBridgeActiveValues]





/-! ## The sole missing constructor and all tangent projections -/





/-! ## Guarded smooth support -/

/-- A structured sample lying in `(n,2n]` whose values avoid the literal
numerical guards is a subset of the guarded smooth row. -/
theorem bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalBridgeActiveValues B ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  intro a ha
  obtain ⟨m, hvalue⟩ :=
    mem_bankPaperCanonicalBridgeActiveValues.mp ha
  subst a
  apply mem_completeRoughRowFiber.mpr
  constructor
  · rw [BankPaperRealization.roughCanonicalGuardedCandidateSet,
      Finset.mem_sdiff, roughRawCandidateSet_eq_Ioc hKh]
    exact ⟨Finset.mem_Ioc.mpr ⟨hlower m, hupper m⟩,
      hnotGuard m⟩
  · exact (completeRoughLabel_eq_one_iff_mem_smoothNumbers
      (B.sampleData.value_pos m)).mpr
        (B.sampleData.value_mem_smoothNumbers m)







/-! ## Frozen layer and quota -/























/-! ## Baseline slack and ambient feasibility -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperProposition87ActualDataConnector -/
section


/-!
# Actual paper data at the Proposition 8.7 / guarded-selector interface

The paper does not use the mass-one normalization of the bridge.  Its
literal active weights are the numbers `z_m^0`, and

`q_n = sum_m z_m^0`.

At a clean numerical coordinate the protected frozen layer may overlap the
active layer.  Consequently `q_n` is not, in general, the sum of the whole
guarded selector on the active support.  This module keeps the two layers
separate.  Every guarded candidate is represented by a frozen tag of weight

`preSelector a - activeSeedAmbient a`,

while Proposition 8.7 evolves the active seed.  Thus the protected overlap
is retained exactly and the combined selector at time zero is the supplied
guarded pre-selector.

The single construction still missing from the finite guarded ledger is
named `BankPaperCanonicalActualActiveMeasureConstructor`.  It asks only for
the paper's active-measure realization: the seed has the canonical
barycentric shape, has eventual paper-scale mass at least one, is supported
on the guarded candidates, and is dominated by the already feasible
pre-selector.  Row integrality, target agreement, band balance, support,
pointwise estimates, and prefix estimates are not repeated in this
constructor; they are derived below from the existing guarded selector and
the Proposition 8.7 path.
-/

open Filter Topology Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## The literal active mass and its sole construction socket -/

























/-! ## The actual scaled bridge data -/









/-! ## Tagged frozen remainder and exact push-forward -/





















/-! ## The initial combined selector -/









/-! ## The literal active marked target and endpoint -/













/-! ## Smooth active support and unchanged complete-rough rows -/









/-- The active seed push-forward vanishes at a coordinate which is not the
value of any active sample tag. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (a : Nat) (ha : forall m : D.Sample, D.value m ≠ a) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a = 0 := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  rw [if_neg (ha m)]













/-! ## Prime support, exact bands, and the derived prefix ledger -/











/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction -/
section


/-!
# Constructing the actual active measure and isolating its irreducible fit

The paper's baseline realization has two logically different parts.

* Once a normalized barycentric target and its literal active mass `q_n`
  are fixed, the active coordinates are forced:

  `z_m^0 = q_n * T.baseline.baseWeight m`.

  Their sum is definitionally finite and is proved below to be exactly
  `q_n`.  No analytic or selector input is needed for this part.

* For a *previously fixed* guarded pre-selector, one must still know that
  the pre-selector carries this active mass at every active numerical
  coordinate.  Under the already available head-pattern separation and
  candidate feasibility, this reduces exactly to the coordinatewise
  inequality

  `q_n * T.baseline.baseWeight m <= preSelector (D.value m)`.

The latter is named `BankPaperCanonicalActualCoordinateFit`.  It is the
irreducible coupling absent from `BankPaperCanonicalGuardedSectionNineContinuation`:
that continuation records feasibility, row sums, and prime residuals, but
no pointwise relation between its selector and the later active baseline.

The module also gives a completely unconditional self-selector
construction, proves the guarded-support part from the existing geometry,
and shows that the older guarded bridge selector constructor supplies the
coordinate fit whenever it is instantiated with the literal active-mass
baseline.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## The forced finite active seed -/



/-- A nonnegative literal mass gives a nonnegative active seed. -/
theorem bankPaperCanonicalScaledActiveSeed_nonneg
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    {q : Real} (hq : 0 <= q) (m : D.Sample) :
    0 <= bankPaperCanonicalScaledActiveSeed T q m := by
  exact mul_nonneg hq (T.baseline.baseWeight_nonneg m)



/-- The ambient push-forward of a nonnegative scaled seed is nonnegative,
without assuming an active-measure constructor. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    {q : Real} (hq : 0 <= q) (a : Nat) :
    0 <= bankPaperCanonicalActiveSeedAmbientWeight D
      (bankPaperCanonicalScaledActiveSeed T q) a := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_nonneg
  intro m _hm
  split_ifs
  · exact bankPaperCanonicalScaledActiveSeed_nonneg T hq m
  · exact le_rfl



/-! ## Canonical finite support and a self-selector witness -/











/-! ## Exact minimization for a fixed guarded pre-selector -/



















/-! ## Guarded geometry and the older bridge-selector constructor -/







/-! ## The literal mass already stored by the paper head simplex -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTangentSlackIntegration -/
section


/-!
# Canonical parameter and endpoint-slack integration for Section 9

This module closes two finite interfaces which occur immediately before the
distributed tangent.

First, it makes one literal choice of `deltaStar` which simultaneously obeys
the complete fixed-factor/precharge budget and the clean-list head-gap
inequality.  Thus the charge terminal and the clean-list theorem no longer
need independently chosen exceptional exponents.

Second, it proves all of the endpoint classification and slack algebra.  A
clean common multiplier puts both endpoints in the guarded broad pool of one
complete rough row, and a nonsmooth such row is active nonexceptional.  On a
nonsmooth row, the displayed absolute bound for the constant correction
density implies the required two-sided selector margin.  On the smooth row,
the protected floor and active ceiling imply the same margin by elementary
addition.

The only construction fact not present in the preceding development is kept
as the explicit proposition
`BankPaperCanonicalGuardedEndpointSlackConstruction`: the actual guarded
selector must agree with the constant broad-row correction off the smooth row,
and its smooth coordinates must have the protected-plus-active decomposition.
No traffic, collision, clean-list cardinality, or final tangent conclusion is
included in that proposition.  The last theorem packages its consequence in
exactly the endpoint-closure and endpoint-slack shape consumed by the
candidate-parametric distributed assembly.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Filter Topology

noncomputable section

/-! ## One exceptional exponent for the charge and tangent arguments -/













namespace BankPaperRealization

/-! ## The explicit guarded nonsmooth correction -/





/-- On the guarded broad pool, the explicit corrected weight is the broad
raw value `beta / L` plus the single rowwise correction density. -/
theorem roughCanonicalGuardedPostchargeRowCorrectedWeight_apply_of_mem
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar W K label alpha beta L a =
      beta / L +
        R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
          deltaStar W K label alpha beta L := by
  rw [roughCanonicalGuardedPostchargeRowCorrectedWeight,
    bankPaperConstantPoolCorrection_apply_of_mem ha,
    roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
        certificate deltaStar W K label ha),
    roughCanonicalGuardedPostchargeCorrectionDensity]

/-- The paper's absolute correction-density bounds leave the exact
two-sided tangent margin on every guarded broad coordinate. -/
theorem roughCanonicalGuardedPostchargeRowCorrectedWeight_twoSidedSlack
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L sigma : Real} {a : Nat}
    (hfloor :
      sigma / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤
        beta / L)
    (hceiling :
      beta / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤
        1 - sigma / L)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    sigma / L ≤
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ∧
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ≤
        1 - sigma / L := by
  let d := R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
    deltaStar W K label alpha beta L
  have hdLower : -|d| ≤ d := neg_abs_le d
  have hdUpper : d ≤ |d| := le_abs_self d
  rw [R.roughCanonicalGuardedPostchargeRowCorrectedWeight_apply_of_mem ha]
  change sigma / L ≤ beta / L + d ∧
    beta / L + d ≤ 1 - sigma / L
  change sigma / L + |d| ≤ beta / L at hfloor
  change beta / L + |d| ≤ 1 - sigma / L at hceiling
  constructor <;> linarith

/-! ## Clean endpoints lie in the appropriate guarded broad pool -/



/-! ## The isolated protected/corrected-selector construction output -/





/-! ## Adapter to the candidate-parametric distributed tangent -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothProtectedAdditiveRefinement -/
section


/-!
# Additive protected refinement on the guarded smooth broad pool

The literal raw selector already has constant broad weight `beta / L`.
The paper splits `beta = betaProt + betaAct`, freezes the first summand,
and replaces the second by the structured active seed.  The earlier
guarded continuation records only the resulting smooth-row integer quota;
it does not retain this pointwise additive identity.

This file restores that identity by an explicit local refinement.  On the
guarded smooth broad pool it sets

`preSelector = betaProt / L + activeSeedAmbient`,

and away from that pool it leaves an already constructed base selector
unchanged.  Thus nonsmooth corrected rows are untouched, while the actual
frozen remainder is definitionally the protected constant `betaProt / L`.
The existing raw-point theorem proves that this constant is precisely the
protected part of the paper's head-compatible raw broad weight.

This closes the positive-remainder and pre-selector-upper algebra without a
new selector assumption.  It deliberately does not claim that replacing an
arbitrary smooth row preserves its integer quota or prime moments: those are
the separate smooth-ledger/active-measure construction obligations.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The explicit protected layer and additive refinement -/









/-- On the clean smooth broad pool, the explicit protected layer is exactly
the paper's head-compatible raw weight with broad parameter `betaProt`. -/
theorem bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha betaProt : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
        deltaStar betaProt a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L a := by
  rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
    B R certificate ha]
  exact (roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
    (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K 1 ha)).symm

















/-! ## Derived active and pre-selector upper bounds -/









/-! ## Exact protected window and actual endpoint -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureAdditiveRefinement -/
section


/-!
# Actual active measure carried by the protected additive refinement

The canonical scaled active seed has exact literal mass `q`.  The protected
additive refinement places its ambient push-forward below the pre-selector
by construction: on every active coordinate it is the active weight plus
the nonnegative protected constant `betaProt / L`.

This file joins those two independent facts.  It proves the minimized
coordinate-fit predicate, candidate nonnegativity, and hence the full
actual-active-measure constructor on the literal guarded candidate set.
The first connector below records the older, stronger hypothesis that all
structured active values lie in the guarded *broad* correction pool.  That
hypothesis is false for the nonzero paper head vertices: the correction pool
is head-free.  The second half of the file therefore gives the literal
paper-faithful placement.  It extends the protected refinement only on the
finite structured active image, which already lies in the guarded smooth
row, and leaves the old refinement unchanged on its whole correction pool.
Its exact capacity predicate is discharged either pointwise or from the
existing cell-density/base-weight bound.

No rounded-selector transport is asserted here.  Replacing a smooth row
can change its integer row sum and prime moments; those equalities are the
separate additive-ledger boundary recorded by the refinement module.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Pointwise fit and feasibility -/





/-! ## Full guarded actual-measure constructor -/



/-! ## Structured placement on the whole guarded smooth row

The broad correction pool is the head-free part of the smooth row, whereas
the structured sample contains the nonzero paper head vertices as well.  The
following selector therefore keeps the protected refinement on its original
pool and, at every remaining structured active value, installs precisely the
active seed (the protected layer is zero there). -/

/-- Fixed physical endpoints in `[1,2]` put every structured value in the
literal interval `(n,2n]`. -/
theorem bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n) :
    (forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m) ∧
      forall m : B.sampleData.Sample,
        B.sampleData.value m <= 2 * B.sampleData.n := by
  constructor
  · intro m
    have hnlo : B.sampleData.n <=
        B.sampleData.lo (B.sampleData.cellOf m).2 := by
      rw [hlo]
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (B.sampleData.n : Real) <=
        I.lower (B.sampleData.cellOf m).2 *
          (B.sampleData.n : Real) by
        nlinarith [show (0 : Real) <= (B.sampleData.n : Real) by
          positivity,
          hlowerOne (B.sampleData.cellOf m).2])
    exact hnlo.trans_lt (B.sampleData.lo_lt_value m)
  · intro m
    let sigma := (B.sampleData.cellOf m).2
    have hvalue : B.sampleData.value m <=
        physicalBound (I.upper sigma) B.sampleData.n := by
      simpa only [sigma, hhi] using B.sampleData.value_le_hi m
    have hupperPos : 0 < I.upper sigma :=
      (I.lower_pos sigma).trans (I.lower_lt_upper sigma)
    have hfloor :
        (physicalBound (I.upper sigma) B.sampleData.n : Real) <=
          I.upper sigma * (B.sampleData.n : Real) := by
      unfold physicalBound
      exact Nat.floor_le
        (mul_nonneg hupperPos.le (by positivity))
    have htwo : I.upper sigma * (B.sampleData.n : Real) <=
        2 * (B.sampleData.n : Real) :=
      mul_le_mul_of_nonneg_right (hupperTwo sigma) (by positivity)
    have hbound : physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n := by
      have hcast := hfloor.trans htwo
      exact_mod_cast hcast
    exact hvalue.trans hbound

/-- Physical fixed-partition endpoints, pointwise rough-guard avoidance, and the rough tail
inequality place every structured head cell in the guarded smooth row. -/
theorem bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  have hbounds := bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    B I hlowerOne hupperTwo hlo hhi
  intro a ha
  apply bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
    B R certificate deltaStar hKh hbounds.1 hbounds.2 hnotGuard
  exact mem_bankPaperCanonicalBridgeActiveValues.mpr
    (mem_bankPaperCanonicalStructuredActiveValues.mp ha)



















/-! ## Exact frozen remainder of the corrected placement -/











/-! ## Exact coordinate capacity and selector feasibility -/





/-- A pointwise `Cactive/L` active-seed bound and one fixed large-`L`
inequality imply the exact placement capacity. -/
theorem bankPaperCanonicalStructuredAdditivePlacementCapacity_of_div_log_bound
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hbetaProt : 0 <= betaProt)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hactiveSeed : forall m : B.sampleData.Sample,
      bankPaperCanonicalScaledActiveSeed T q m <= Cactive / B.L)
    (hlarge : betaProt + Cactive <= B.L) :
    BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q := by
  constructor
  · have hbetaLe : betaProt <= B.L :=
      (le_add_of_nonneg_right hCactive).trans hlarge
    calc
      betaProt / B.L <= B.L / B.L :=
        div_le_div_of_nonneg_right hbetaLe B.L_pos.le
      _ = 1 := div_self (ne_of_gt B.L_pos)
  · intro m
    have hprotected :
        bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
            deltaStar betaProt (B.sampleData.value m) <=
          betaProt / B.L := by
      by_cases hpool : B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1
      · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate hpool]
      · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
          B R certificate hpool]
        exact div_nonneg hbetaProt B.L_pos.le
    calc
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
            deltaStar betaProt (B.sampleData.value m) +
          bankPaperCanonicalScaledActiveSeed T q m <=
        betaProt / B.L + Cactive / B.L :=
          add_le_add hprotected (hactiveSeed m)
      _ = (betaProt + Cactive) / B.L := by ring
      _ <= B.L / B.L :=
        div_le_div_of_nonneg_right hlarge B.L_pos.le
      _ = 1 := div_self (ne_of_gt B.L_pos)



/-! ## Full guarded constructor with the corrected placement -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothAdditivePlacement -/
section


/-!
# Paper-faithful placement boundary for the guarded smooth refinement

The smooth bridge in the paper does not preserve the medium-prime moments
of an earlier provisional selector.  It freezes the protected layer,
redistributes the active mass while preserving the smooth-row ledger and
the moments outside the tangent band, and then fits the medium-prime band
moments.  Proposition 8.7 supplies that latter fit.

Accordingly, the pre-selector part of the actual endpoint theorem needs
only complete-row integrality and deficit support outside the medium-prime
band.  Its older statement accepted a full rounded-selector tangent input,
although the proof used only those two fields.  This file records the
weaker exact theorem, constructs the minimized ledger from the paper's two
literal zero-head cells, and proves the exact scaled structured head-cell
moments.  It then resolves the support boundary--the nonzero head cells lie
in the smooth row, not in its head-free correction subpool--by transporting
a signed ledger over the whole smooth row for the corrected selector.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization



/-! ## Exact finite algebra for the two zero-head pools -/





















/-! ## The head-free correction-pool ledger -/











/-! ## Structured head-cell realization -/

/-- Summing a uniform baseline coordinate statistic which depends only on
the structured cell recovers the corresponding cell-mass sum. -/
theorem sum_baselineBaseWeight_mul_cellFunction
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head}
    (A : BaselineAllocation D) (f : Cell Head -> Real) :
    (∑ m : D.Sample, A.baseWeight m * f (D.cellOf m)) =
      ∑ cell : Cell Head, A.cellMass cell * f cell := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro cell _hcell
  simp only [BaselineAllocation.baseWeight, StructuredSampleData.cellOf]
  have hcard : (Fintype.card (D.SampleAt cell) : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.sampleAt_card_pos cell)
  change (∑ _ : D.SampleAt cell,
    A.cellMass cell / (Fintype.card (D.SampleAt cell) : ℝ) * f cell) =
      A.cellMass cell * f cell
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

/-- The canonical scaled seed realizes every prescribed head-tag linear
moment with the literal active-mass factor in front. -/
theorem sum_bankPaperCanonicalScaledActiveSeed_mul_headFunction
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    (q : Real) (phi : Head -> Real) :
    (∑ m : D.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          phi (D.cellOf m).1) =
      q * ∑ h : Head, T.beta h * phi h := by
  calc
    (∑ m : D.Sample,
        bankPaperCanonicalScaledActiveSeed T q m *
          phi (D.cellOf m).1) =
      q * ∑ m : D.Sample,
        T.baseline.baseWeight m * phi (D.cellOf m).1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalScaledActiveSeed
      ring
    _ = q * ∑ cell : Cell Head,
        T.baseline.cellMass cell * phi cell.1 := by
      apply congrArg (q * ·)
      simpa using
        (sum_baselineBaseWeight_mul_cellFunction
          T.baseline (fun cell => phi cell.1))
    _ = q * ∑ cell : Cell Head,
        T.baseline.normalizedCellMass cell * phi cell.1 := by
      apply congrArg (q * ·)
      apply Finset.sum_congr rfl
      intro cell _hcell
      unfold BaselineAllocation.normalizedCellMass
      rw [T.baseline_totalMass, div_one]
    _ = q * ∑ h : Head, T.beta h * phi h := by
      rw [T.headMoment phi]

/-- Weighted ambient push-forward over a support containing all structured
values is exactly the corresponding tagged weighted sum. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : forall m : D.Sample, D.value m ∈ support)
    (p : Nat) :
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight D seed a *
          valuation p a) =
      ∑ m : D.Sample, seed m * valuation p (D.value m) := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim

/-- The scaled structured head-simplex seed has exactly the unnormalized
head-prime moment stored in `HeadSimplexReserve`.  This is the finite
coordinate version of the paper's head-cell realization. -/
theorem sum_bankPaperCanonicalScaledActiveSeed_mul_paperHeadValuation
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    (p : {p : Nat // p ∈ P}) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T Rhead.activeMass m *
          valuation p.1 (B.sampleData.value m)) = Rhead.target p := by
  dsimp only
  let T := B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical
  have hvaluation : forall m : B.sampleData.Sample,
      valuation p.1 (B.sampleData.value m) =
        (PaperHeadSimplex.exponent P Rhead.exponent
          (B.sampleData.cellOf m).1 p.1 : Real) := by
    intro m
    have hpMem : p.1 ∈
        (B.sampleData.pattern (B.sampleData.cellOf m).1).primes := by
      rw [hpattern]
      exact p.2
    have hm := B.sampleData.value_matches_head m p.1 hpMem
    simpa [valuation, hpattern, PaperHeadSimplex.pattern] using
      congrArg (fun k : Nat => (k : Real)) hm
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T Rhead.activeMass m *
          valuation p.1 (B.sampleData.value m)) =
      ∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T Rhead.activeMass m *
          (PaperHeadSimplex.exponent P Rhead.exponent
            (B.sampleData.cellOf m).1 p.1 : Real) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [hvaluation m]
    _ = Rhead.activeMass *
        ∑ h : PaperHeadSimplex.Tag P,
          T.beta h *
            (PaperHeadSimplex.exponent P Rhead.exponent h p.1 : Real) :=
      sum_bankPaperCanonicalScaledActiveSeed_mul_headFunction
        T Rhead.activeMass
          (fun h =>
            (PaperHeadSimplex.exponent P Rhead.exponent h p.1 : Real))
    _ = Rhead.activeMass * (Rhead.target p / Rhead.activeMass) := by
      apply congrArg (Rhead.activeMass * ·)
      change (∑ h : PaperHeadSimplex.Tag P,
        Rhead.beta h *
          (PaperHeadSimplex.exponent P Rhead.exponent h p.1 : Real)) = _
      exact Rhead.beta_exponent_moment p
    _ = Rhead.target p := by
      field_simp [ne_of_gt Rhead.activeMass_pos]

/-- Ambient form of the same exact structured head-cell realization. -/
theorem sum_bankPaperCanonicalScaledActiveSeedAmbient_mul_paperHeadValuation
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    (support : Finset Nat)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ support)
    (p : {p : Nat // p ∈ P}) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a *
          valuation p.1 a) = Rhead.target p := by
  dsimp only
  rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
    B.sampleData _ support hvalues p.1]
  exact sum_bankPaperCanonicalScaledActiveSeed_mul_paperHeadValuation
    B hprime Rhead I hlo hhi Kphysical hpattern p









/-! ## Exact support boundary -/



/-! ## Signed whole-smooth-row placement ledger -/



































end BankPaperRealization

/-! ## Weaker actual-endpoint preselector interface -/



namespace BankPaperRealization







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellOuterCapacityConnector -/
section


/-!
# Outer asymptotic capacity for the two zero-head cells

The finite two-cell producer reduces feasibility to one lower and one upper
scalar inequality in each physical sign.  This file supplies those
inequalities from the already constructed paper-scale inputs.

The actual post-guard mass is bounded below and above on the
`secondOrderScale` scale.  The combined nearest-integer and height change is
little-o of that scale.  A uniform positive cell-mass margin therefore
absorbs every removal.  On the other side, `secondOrderScale = o(n)` and the
canonical guard-deleted cell-density theorem leave enough room below the
protected ceiling.

The terminal statements use the same local canonical-data equality and
cell-mass-margin argument as Proposition 8.7.  No new asymptotic predicate or
family-identification assumption is introduced.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Scale and cell-mass preliminaries -/





/-- Every literal canonical baseline cell mass is at most one. -/
theorem bankPaperCanonical_baseline_cellMass_le_one
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head}
    (T : BarycentricTarget D) (cell : Cell Head) :
    T.baseline.cellMass cell <= 1 := by
  calc
    T.baseline.cellMass cell =
        T.baseline.normalizedCellMass cell := by
      symm
      unfold BaselineAllocation.normalizedCellMass
      rw [T.baseline_totalMass, div_one]
    _ <= 1 := by
      rw [← T.baseline.normalizedCellMass_sum]
      exact Finset.single_le_sum
        (fun d _hd => (T.baseline.normalizedCellMass_pos d).le)
        (Finset.mem_univ cell)

/-! ## The combined cell change is negligible -/





/-! ## A common positive density for the two zero-head cells -/







/-! ## Outer scalar capacity -/



/-! ## Feeding the finite producer -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGlobalCorrectedSourceSelector -/
section


/-!
# Global corrected source selector

The original two-zero-cell source selector uses the protected-plus-active
weight on the smooth guarded broad pool and the old active ambient weight
everywhere else.  That is the right source for the Section 8 moment ledger,
but it is not the selector required by the Section 9 endpoint theorem on a
nonsmooth active row.

This file makes a rowwise compatible global replacement.  Off the smooth
broad pool it keeps the old ambient weight on complete-rough label `1`, and
uses the already constructed postcharge corrected row weight on active
nonexceptional labels, while exceptional labels are zero.  Consequently:

* once structured active values are known to lie in the complete smooth
  row, the source still agrees with the old ambient weight at every such
  coordinate outside the smooth broad pool, so the existing two-zero-cell
  prebridge ledger applies unchanged;
* every active nonsmooth guarded broad coordinate is exactly the explicit
  postcharge corrected row weight; and
* after structured placement, the two exact `hpreNonsmooth` and
  `hpreUpper` interfaces consumed by the endpoint-slack theorem are exposed.

The exact corrected-weight identity uses the literal active-nonexceptional
classification; preservation by structured placement additionally uses
smooth-row support of the structured active values.  The smooth upper theorem
honestly retains the pointwise `O(1 / L)` upper bound for the placement seed.
Existing two-zero-cell capacity only bounds the resulting selector by `1`;
it does not imply this sharper estimate.

On an active nonexceptional complete label, the outside selector intentionally
uses the full corrected-row weight, including its raw-weight branch outside
the guarded broad correction pool.  This is the rowwise selector whose total
is controlled by the postcharge construction, rather than a pointwise-only
patch of the old ambient source.  A rounded-selector input for this global
source remains explicit below; it is not manufactured from local slack.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Arbitrary-seed push-forward -/

/-- Numerical head-pattern separation makes the structured value map
injective, so the ambient push-forward of an arbitrary seed at an occupied
coordinate is exactly the corresponding tagged weight.  This elementary
form is kept below the Section 8 one-shot layer so that the latter can reuse
the global source connector without an import cycle. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (hsep : D.HeadPatternsSeparated) (m : D.Sample) :
    bankPaperCanonicalActiveSeedAmbientWeight D seed (D.value m) =
      seed m := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  rw [Finset.sum_eq_single m]
  · simp
  · intro k _hk hkm
    rw [if_neg]
    intro hvalue
    exact hkm (D.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

/-! ## The global outside selector -/









/-! ## The global source and its exact rowwise values -/







/-! ## Compatibility with the Section 8 prebridge ledger -/



/-! ## Full Section 8 placement with the global source -/







/-! ## Exact endpoint-slack inputs after structured placement -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateConnector -/
section


/-!
# Nearest-integer source state for the frozen-top selector

The finite frozen-top source at mass `qTilde` has the paper's literal
smooth-row mass, but that mass need not be an integer.  The initialization
step replaces `qTilde` by

`q0 = nearestInteger(mFrozen + qTilde) - mFrozen`.

This connector proves the exact part of that handoff:

* changing the scaled seed from `qTilde` to `q0` changes no nonsmooth row;
* the new smooth-row total is the declared nearest integer;
* the charged nonsmooth-row equations therefore imply integrality of every
  complete rough row; and
* feasibility and exact target agreement outside the tangent prime band
  then package the result as `BankPaperCanonicalSelectorSourceState`.

The last two properties are retained as explicit premises.  They are not
consequences of row-mass rounding: feasibility is pointwise, while target
agreement is a prime-valuation identity.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The exact frozen mass and nearest-integer source -/













/-! ## Nonsmooth rows are independent of the active seed -/



/-- On an active nonexceptional nonsmooth guarded row, the frozen-top source
is the explicit postcharge corrected row weight. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha betaTotal : Real)
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed a =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha betaTotal B.L a := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hactive.1 (haLabel.symm.trans haSmoothLabel)
  have haNotOne :
      completeRoughLabel (yNat B.sampleData.n) a ≠ 1 := by
    intro haOne
    exact hactive.1 (haLabel.symm.trans haOne)
  have hnonexceptional :
      ¬ RoughCanonicalExceptionalLabel
        B.sampleData.n deltaStar label :=
    not_lt_of_ge hactive.2
  unfold bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
  unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
  rw [if_neg hnotSmoothPool]
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
  rw [if_neg haNotOne, haLabel, if_neg hnonexceptional]

/-- On an exceptional nonsmooth guarded row, the frozen-top source is
pointwise zero. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_exceptionalNonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha betaTotal : Real)
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hlabel : label ≠ 1)
    (hexceptional :
      RoughCanonicalExceptionalLabel B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed a = 0 := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hlabel (haLabel.symm.trans haSmoothLabel)
  have haNotOne :
      completeRoughLabel (yNat B.sampleData.n) a ≠ 1 := by
    intro haOne
    exact hlabel (haLabel.symm.trans haOne)
  unfold bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
  unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
  rw [if_neg hnotSmoothPool]
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
  rw [if_neg haNotOne, haLabel, if_pos hexceptional]



/-! ## Exact smooth and nonsmooth row ledgers -/











/-! ## Exact feasibility transport through the two zero cells -/



/-! ## Complete-row integrality and the source-state handoff -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenSourceFeasibilityReductionConnector -/
section


/-!
# Feasibility reduction for the frozen-top sources

Exceptional nonsmooth rows of the frozen-top source are now pointwise zero.
Thus feasibility on the whole guarded candidate set reduces exactly to two
genuine inputs:

* feasibility on the guarded smooth row; and
* feasibility of the explicit corrected weight on active nonexceptional
  nonsmooth rows.

The first pair of finite theorems records this reduction for the general
frozen-top source and for its nearest-integer rounded specialization.  The
last pair discharges the active-row premise from the existing two-sided
slack theorem: on the guarded broad correction pool that theorem supplies
the box bounds, while off the pool the corrected weight is the feasible raw
weight.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Feasibility of one active corrected row -/

/-- Two-sided slack on the guarded broad correction pool, together with
the raw parameter box, proves `[0,1]` feasibility on the entire guarded
active row.  Outside the correction pool the corrected weight is literally
the raw head-compatible weight. -/
theorem
    roughCanonicalGuardedPostchargeRowCorrectedWeight_mem_unitInterval_of_twoSidedSlack
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L sigma : Real}
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbeta : 0 <= beta / L ∧ beta / L <= 1)
    (hsigma : 0 <= sigma / L)
    (hfloor :
      sigma / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| <=
        beta / L)
    (hceiling :
      beta / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| <=
        1 - sigma / L)
    {a : Nat}
    (_ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    0 <=
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ∧
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a <= 1 := by
  by_cases haPool :
      a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K label
  · have hslack :=
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight_twoSidedSlack
        hfloor hceiling haPool
    exact
      ⟨hsigma.trans hslack.1,
        hslack.2.trans (sub_le_self 1 hsigma)⟩
  · rw [roughCanonicalGuardedPostchargeRowCorrectedWeight,
      bankPaperConstantPoolCorrection_apply_of_not_mem haPool]
    exact roughHeadCompatibleRawWeight_mem_unitInterval halpha hbeta a

/-! ## Classification reduction on the guarded candidate set -/

/-- The general frozen-top source is feasible on the full guarded candidate
set once its smooth row and its explicit active nonexceptional corrected
rows are feasible.  Exceptional nonsmooth rows require no premise because
the source is pointwise zero there. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_active
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (hsmooth : ∀ a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a <= 1)
    (hactive : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          0 <=
              R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha beta B.L a ∧
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha beta B.L a <= 1) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a <= 1 := by
  intro a ha
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have haSmooth :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩)
    exact hsmooth a haSmooth
  · have haRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K
          (completeRoughLabel (yNat B.sampleData.n) a) := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩)
    rcases roughCanonical_activeNonexceptional_or_exceptional
        (n := B.sampleData.n) (deltaStar := deltaStar) hlabel with
      hactiveLabel | hexceptional
    · rw [
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
          (K := K) B R certificate deltaStar betaProt alpha beta oldSeed
            hactiveLabel haRow]
      exact hactive _ hactiveLabel a haRow
    · rw [
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_exceptionalNonsmoothRow
          (K := K) B R certificate deltaStar betaProt alpha beta oldSeed
            hlabel hexceptional haRow]
      exact ⟨le_rfl, zero_le_one⟩



/-! ## Closing the active premise by two-sided slack -/

/-- The raw parameter box and the existing two-sided correction-pool slack
close the active-row premise in the general frozen-top feasibility
reduction. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_twoSidedSlack
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta sigma : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbeta : 0 <= beta / B.L ∧ beta / B.L <= 1)
    (hsigma : 0 <= sigma / B.L)
    (hsmooth : ∀ a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a <= 1)
    (hfloor : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L)
    (hceiling : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a <= 1 := by
  apply
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_active
      (K := K) B R certificate deltaStar betaProt alpha beta oldSeed hsmooth
  intro label hactiveLabel a ha
  exact
    roughCanonicalGuardedPostchargeRowCorrectedWeight_mem_unitInterval_of_twoSidedSlack
      (R := R) (certificate := certificate) halpha hbeta hsigma
        (hfloor label hactiveLabel) (hceiling label hactiveLabel) ha



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenSmoothFeasibilityConnector -/
section


/-!
# Smooth-row feasibility for the frozen-top source

The classification theorem for the frozen-top source leaves one local
premise on complete rough label `1`.  This file discharges that premise for
the literal scaled active seed.

There are two elementary points.

* At a surviving smooth coordinate in the broad lower block, the protected
  layer is exactly the raw head-compatible weight.  If the coordinate is
  head-free it lies in the guarded smooth correction pool; otherwise both
  weights vanish.
* Away from the structured active image the ambient scaled seed vanishes.
  On the image, the existing
  `BankPaperCanonicalStructuredAdditivePlacementCapacity` is precisely the
  required upper bound.

Thus the only geometric input is that the structured active values lie in
the broad lower block.  This is the finite form of the strict physical
upper-endpoint gap already used in the canonical Section 8 geometry.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Broad support from the physical endpoint gap -/

/-- The same strict upper-endpoint gap used by the canonical Section 8
geometry puts every structured sample value in the broad lower block.

This is stated separately because the earlier geometry projection exports
smooth-row support but only exports guarded-broad membership for the two
zero-head cells. -/
theorem
    bankPaperCanonicalStructuredValue_mem_roughBroadLowerBlock_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (I : PhysicalIntervals) (h K : Nat)
    (hlowerOne : ∀ sigma, 1 <= I.lower sigma)
    (hupperTwo : ∀ sigma, I.upper sigma <= 2)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hupperBroad : ∀ sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n - K * h) :
    ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n h K := by
  have hbounds :=
    bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
      B I hlowerOne hupperTwo hlo hhi
  intro m
  rw [roughBroadLowerBlock, Finset.mem_Ioc]
  refine ⟨hbounds.1 m, ?_⟩
  calc
    B.sampleData.value m <=
        B.sampleData.hi (B.sampleData.cellOf m).2 :=
      B.sampleData.value_le_hi m
    _ = physicalBound (I.upper (B.sampleData.cellOf m).2)
          B.sampleData.n :=
      hhi (B.sampleData.cellOf m).2
    _ <= 2 * B.sampleData.n - K * h :=
      hupperBroad (B.sampleData.cellOf m).2

/-! ## Identification of the protected layer on the broad smooth row -/

/-- On every surviving smooth-row coordinate in the broad lower block, the
explicit protected layer equals the raw head-compatible weight with broad
parameter `betaProt`.

The existing pointwise theorem handles the head-free case.  In the
non-head-free case the coordinate is outside the correction pool and both
sides are zero. -/
theorem
    bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha betaProt : Real} {a : Nat}
    (haSmooth :
      a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (haBroad :
      a ∈ roughBroadLowerBlock B.sampleData.n
        (upperTailLength c B.sampleData.n) K) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
        B R certificate deltaStar betaProt a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L a := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus B.sampleData.W)
  · have haCandidate :
        a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K :=
      (mem_completeRoughRowFiber.mp haSmooth).1
    have haSurvives :
        a ∉ R.roughCanonicalGuardSet certificate deltaStar :=
      (Finset.disjoint_left.mp
        (R.roughCanonicalGuardedCandidateSet_disjoint_guardSet
          certificate deltaStar K)) haCandidate
    have haRawPool :
        a ∈ roughCanonicalBroadCorrectionPool B.sampleData.W
          B.sampleData.n (upperTailLength c B.sampleData.n) K
            (yNat B.sampleData.n) 1 := by
      apply mem_completeRoughRowFiber.mpr
      exact
        ⟨mem_roughHeadFree.mpr ⟨haBroad, hcop⟩,
          (mem_completeRoughRowFiber.mp haSmooth).2⟩
    have haPool :
        a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      rw [roughCanonicalGuardedBroadCorrectionPool, Finset.mem_sdiff]
      exact ⟨haRawPool, haSurvives⟩
    exact
      bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem
        B R certificate haPool
  · have hnotPool :
        a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      intro haPool
      have haRawPool :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
          certificate deltaStar B.sampleData.W K 1 haPool
      have haHeadFree :=
        (mem_completeRoughRowFiber.mp haRawPool).1
      exact hcop (mem_roughHeadFree.mp haHeadFree).2
    rw [
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        B R certificate hnotPool]
    simp [roughHeadCompatibleRawWeight, hcop]

/-! ## The atomic smooth-row premise -/

/-- The exact structured-placement capacity closes feasibility of the
literal frozen-top source on complete rough label `1`.

Inactive coordinates use the ordinary raw parameter box.  At an active
coordinate, broad support identifies the raw layer with the protected layer,
and head-pattern separation identifies the ambient push-forward with the
corresponding tagged scaled seed. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_feasible_of_scaledSeedCapacity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal q : Real)
    (hq : 0 <= q)
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbetaProt : 0 <= betaProt / B.L ∧ betaProt / B.L <= 1)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (hcapacity :
      BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
        B R certificate deltaStar betaProt T q) :
    ∀ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a <= 1 := by
  intro a haSmooth
  rw [
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
      B R certificate (bankPaperCanonicalScaledActiveSeed T q) haSmooth]
  have hraw :=
    roughHeadCompatibleRawWeight_mem_unitInterval
      (W := B.sampleData.W) (n := B.sampleData.n)
      (h := upperTailLength c B.sampleData.n) (K := K)
      (α := alpha) (β := betaProt) (L := B.L)
      halpha hbetaProt a
  have hambientNonneg :
      0 <= bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
        (bankPaperCanonicalScaledActiveSeed T q) a :=
    bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg T hq a
  constructor
  · exact add_nonneg hraw.1 hambientNonneg
  · by_cases hactive :
        a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
    · obtain ⟨m, rfl⟩ :=
        mem_bankPaperCanonicalStructuredActiveValues.mp hactive
      rw [
        ←
          bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
            B R certificate haSmooth (hactiveBroad m),
        bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
          B.sampleData (bankPaperCanonicalScaledActiveSeed T q) hsep m]
      exact hcapacity.2 m
    · have hambientZero :
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q) a = 0 := by
        apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
        intro m hma
        exact hactive
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      rw [hambientZero, add_zero]
      exact hraw.2

/-! ## Full finite feasibility -/



/-- A pointwise `Cactive / L` bound and the scalar room
`betaProt + Cactive <= L` are the existing parameter-box form of the exact
capacity predicate.  Combining them with the two-sided nonsmooth slack
theorem gives feasibility on the entire guarded candidate set without a
separate smooth-row premise. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_scaledSeedDivLog_of_twoSidedSlack
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal q sigma Cactive : Real)
    (hq : 0 <= q)
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbetaProt : 0 <= betaProt)
    (hbetaTotal : 0 <= betaTotal / B.L ∧ betaTotal / B.L <= 1)
    (hsigma : 0 <= sigma / B.L)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (hCactive : 0 <= Cactive)
    (hseedUpper : ∀ m : B.sampleData.Sample,
      bankPaperCanonicalScaledActiveSeed T q m <= Cactive / B.L)
    (hlarge : betaProt + Cactive <= B.L)
    (hfloor : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha betaTotal B.L| <=
          betaTotal / B.L)
    (hceiling : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        betaTotal / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha betaTotal B.L| <=
          1 - sigma / B.L) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a <= 1 := by
  have hcapacity :
      BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
        B R certificate deltaStar betaProt T q :=
    bankPaperCanonicalStructuredAdditivePlacementCapacity_of_div_log_bound
      (K := K) B R certificate deltaStar betaProt T q hbetaProt
        Cactive hCactive hseedUpper hlarge
  have hbetaProtBox :
      0 <= betaProt / B.L ∧ betaProt / B.L <= 1 :=
    ⟨div_nonneg hbetaProt B.L_pos.le, hcapacity.1⟩
  apply
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_twoSidedSlack
      (K := K) B R certificate deltaStar betaProt alpha betaTotal sigma
        (bankPaperCanonicalScaledActiveSeed T q)
        halpha hbetaTotal hsigma
  · exact
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_feasible_of_scaledSeedCapacity
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal q
          hq halpha hbetaProtBox hsep hactiveBroad hcapacity
  · exact hfloor
  · exact hceiling

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenChargedRowsConnector -/
section


/-!
# Charged nonsmooth rows for the frozen-top source

The frozen-top `qTilde` source now vanishes pointwise on every exceptional
nonsmooth row.  On an active nonexceptional row it is the literal guarded
constant-pool correction.  Consequently a one-coordinate lower bound for
each guarded broad correction pool is enough to manufacture the complete
charged-row realization.

The finite theorem below keeps that capacity hypothesis explicit.  The
eventual wrapper supplies it from the intrinsic raw broad-pool surplus and
the canonical three-coordinate guard census.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Finite charged-row producer -/

/-- The literal frozen-top `qTilde` source realizes every charged nonsmooth
row once each active nonexceptional complete label has a nonempty guarded
broad correction pool.

The active-row identity is the generic constant-pool correction sum.
Exceptional rows are pointwise zero by construction. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_chargedNonsmoothRows_of_activeCapacity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hcapacity : ∀ label,
      IsCompleteRoughLabel (yNat B.sampleData.n) label ->
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
            B.sampleData.W K label 1) :
    BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde)) := by
  constructor
  · intro label hlabelMem hactive
    have hcomplete : IsCompleteRoughLabel
        (yNat B.sampleData.n) label :=
      isCompleteRoughLabel_of_canonicalCompleteRoughRow
        (⟨label, hlabelMem⟩ :
          CanonicalCompleteRoughRow (yNat B.sampleData.n)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
    have hpoolCapacity := hcapacity label hcomplete hactive
    have hpoolNonempty :
        (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
          B.sampleData.W K label).Nonempty := by
      apply Finset.card_pos.mp
      exact hpoolCapacity
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
            deltaStar B.sampleData.W K label alpha betaTotal B.L a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact
            bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
              (K := K) B R certificate deltaStar betaProt alpha betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde) hactive ha
      _ = R.roughCanonicalPostchargeRowTarget deltaStar label := by
        simpa only [roughCanonicalGuardedPostchargeRowCorrectedWeight] using
          (sum_bankPaperConstantPoolCorrection_eq_target
            (x := roughHeadCompatibleRawWeight B.sampleData.W
              B.sampleData.n (upperTailLength c B.sampleData.n) K
                alpha betaTotal B.L)
            (target := R.roughCanonicalPostchargeRowTarget deltaStar label)
            (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
              certificate deltaStar B.sampleData.W K label)
            hpoolNonempty)
  · intro label _hlabelMem hlabel hexceptional
    apply Finset.sum_eq_zero
    intro a ha
    exact
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_exceptionalNonsmoothRow
        (K := K) B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde)
          hlabel hexceptional ha

/-! ## Eventual capacity supplier -/

/-- Eventually the intrinsic guarded broad-pool capacity supplies the
charged nonsmooth rows of every literal frozen-top `qTilde` source with the
displayed physical index and head cutoff. -/
theorem
    eventually_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_chargedNonsmoothRows
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (depth W K : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        forall
          (R : BankPaperRealization B.sampleData.n
            (upperEndpoint B.sampleData.n
              (upperTailLength c B.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth
            B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth))
          (T : BarycentricTarget B.sampleData)
          (betaProt alpha betaTotal qTilde : Real),
          BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) R certificate deltaStar
              (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
                (K := K) B R certificate deltaStar betaProt alpha betaTotal
                  (bankPaperCanonicalScaledActiveSeed T qTilde)) := by
  have Hcapacity :=
    BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
      W K 1 hc hdelta
  filter_upwards [Hcapacity,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_yNat_lt_centralAnchorCutoff depth]
      with n hcapacityN hnCutoff hyCutoff
  intro B hBn hBW R certificate T betaProt alpha betaTotal qTilde
  subst n
  refine
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_chargedNonsmoothRows_of_activeCapacity
      (K := K) B R certificate T deltaStar betaProt alpha betaTotal
        qTilde ?_
  intro label hcomplete hactive
  simpa only [hBW] using
    (hcapacityN depth R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth) R certificate hnCutoff hyCutoff
        label hcomplete hactive).2.1

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenSelectorTailSupportReductionConnector -/
section


/-!
# Selector-tail support reduction for the frozen-top sources

Outside the medium-prime band there are two disjoint finite mechanisms.

* At a head prime `q ≤ W`, every raw or constant-pool correction term has
  zero `q`-valuation.  The source moment is therefore exactly the moment of
  the scaled structured seed, hence `Rhead.target`.
* At a high prime `yNat n < q`, factorization is constant on each complete
  rough row.  Charged nonsmooth-row totals, together with postcharge row
  capacity for unattained active rows, identify the source moment with the
  selector-tail target ledger.

Thus the only extra low-prime datum is the literal compatibility

`Rhead.target p =
  (certificate.selectorTailTarget R fixed).factorization p`.

The finite theorems below first expose the low/high reductions separately,
then package selector-tail support for both the literal `qTilde` source and
its nearest-integer rounded counterpart.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Head-prime vanishing -/

/-- A head-compatible raw coordinate has zero weighted valuation at every
prime in the complete head product. -/
theorem
    roughHeadCompatibleRawWeight_mul_factorization_eq_zero_of_headPrime
    {W n h K q a : Nat} {alpha beta ell : Real}
    (hqPrime : q.Prime) (hqW : q <= W) :
    roughHeadCompatibleRawWeight W n h K alpha beta ell a *
        (a.factorization q : Real) = 0 := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus W)
  · have hqHead : q ∈ primesUpTo W :=
      mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
    have hqDvd : q ∣ roughHeadModulus W := by
      unfold roughHeadModulus
      exact Finset.dvd_prod_of_mem (fun r : Nat => r) hqHead
    have haq : Nat.Coprime a q :=
      Nat.Coprime.of_dvd_right hqDvd hcop
    have hfactorization : a.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (hqPrime.coprime_iff_not_dvd.mp haq.symm)
    rw [hfactorization]
    ring
  · simp [roughHeadCompatibleRawWeight, hcop]

/-- Every coordinate in any guarded broad correction row—not only the
smooth row—has zero valuation at a head prime. -/
theorem factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime_label
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar : Real} {q a : Nat}
    (hqPrime : q.Prime) (hqW : q <= B.sampleData.W)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    a.factorization q = 0 := by
  have haRaw :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K label ha
  have haData := mem_completeRoughRowFiber.mp haRaw
  have haHeadFree := mem_roughHeadFree.mp haData.1
  have hqHead : q ∈ primesUpTo B.sampleData.W :=
    mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
  have hqDvd : q ∣ roughHeadModulus B.sampleData.W := by
    unfold roughHeadModulus
    exact Finset.dvd_prod_of_mem (fun r : Nat => r) hqHead
  have haq : Nat.Coprime a q :=
    Nat.Coprime.of_dvd_right hqDvd haHeadFree.2
  exact Nat.factorization_eq_zero_of_not_dvd
    (hqPrime.coprime_iff_not_dvd.mp haq.symm)

/-- The literal guarded postcharge correction has zero weighted valuation
at every head prime, independently of its row target and density. -/
theorem
    roughCanonicalGuardedPostchargeRowCorrectedWeight_mul_factorization_eq_zero_of_headPrime
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha beta : Real} {q a : Nat}
    (hqPrime : q.Prime) (hqW : q <= B.sampleData.W) :
    R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar B.sampleData.W K label alpha beta B.L a *
        (a.factorization q : Real) = 0 := by
  unfold roughCanonicalGuardedPostchargeRowCorrectedWeight
  unfold bankPaperConstantPoolCorrection
  by_cases haPool :
      a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K label
  · rw [if_pos haPool,
      factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime_label
        B R certificate hqPrime hqW haPool]
    ring
  · rw [if_neg haPool]
    simpa using
      (roughHeadCompatibleRawWeight_mul_factorization_eq_zero_of_headPrime
        (W := B.sampleData.W) (n := B.sampleData.n)
        (h := upperTailLength c B.sampleData.n) (K := K)
        (alpha := alpha) (beta := beta) (ell := B.L)
        (q := q) (a := a) hqPrime hqW)

/-- On the guarded candidate set, the complete frozen-top source has the
same head-prime moment pointwise as its ambient structured seed. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_ambient_of_headPrime
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {q a : Nat} (hqPrime : q.Prime) (hqW : q <= B.sampleData.W)
    (ha : a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a *
        (a.factorization q : Real) =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a *
        (a.factorization q : Real) := by
  classical
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have haSmooth :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩)
    rw [
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate oldSeed haSmooth]
    have hraw :=
      roughHeadCompatibleRawWeight_mul_factorization_eq_zero_of_headPrime
        (W := B.sampleData.W) (n := B.sampleData.n)
        (h := upperTailLength c B.sampleData.n) (K := K)
        (alpha := alpha) (beta := betaProt) (ell := B.L)
        (q := q) (a := a) hqPrime hqW
    calc
      (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a) *
          (a.factorization q : Real) =
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha betaProt B.L a *
            (a.factorization q : Real) +
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a *
            (a.factorization q : Real) := by ring
      _ = bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a * (a.factorization q : Real) := by
        rw [hraw]
        ring
  · have hnotSmoothPool :
        a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      intro haPool
      have haSmooth :
          a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
          certificate deltaStar B.sampleData.W K 1 haPool
      exact hlabel (mem_completeRoughRowFiber.mp haSmooth).2
    have hambientZero :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      exact hlabel (mem_completeRoughRowFiber.mp hmSmooth).2
    rw [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
      bankPaperCanonicalTwoZeroHeadCellSourceSelector,
      if_neg hnotSmoothPool,
      bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
      if_neg hlabel]
    by_cases hexceptional :
        RoughCanonicalExceptionalLabel B.sampleData.n deltaStar
          (completeRoughLabel (yNat B.sampleData.n) a)
    · rw [if_pos hexceptional, hambientZero]
    · rw [if_neg hexceptional, hambientZero,
        roughCanonicalGuardedPostchargeRowCorrectedWeight_mul_factorization_eq_zero_of_headPrime
          B R certificate hqPrime hqW]
      ring

/-- The whole literal frozen-top source moment at a head prime is exactly
the corresponding reserve target. -/
theorem
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_headTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (p : {p : Nat // p ∈ P}) (hpW : p.1 <= B.sampleData.W) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha beta
              (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a *
          (a.factorization p.1 : Real)) =
      Rhead.target p := by
  dsimp only
  let T :=
    B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro m
    exact (mem_completeRoughRowFiber.mp
      (hactiveSmooth
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩))).1
  calc
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha beta
              (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a *
          (a.factorization p.1 : Real)) =
      ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass) a *
          (a.factorization p.1 : Real) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_ambient_of_headPrime
          (K := K) B R certificate deltaStar betaProt alpha beta
            (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass)
            hactiveSmooth (hprime p.1 p.2) hpW ha
    _ = Rhead.target p := by
      simpa only [T, valuation] using
        (sum_bankPaperCanonicalScaledActiveSeedAmbient_mul_paperHeadValuation
          B hprime Rhead I hlo hhi Kphysical hpattern
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            hvalues p)

/-- Low-prime selector-tail closure.  The displayed reserve/target
compatibility is the only premise not supplied by the finite head
realization itself. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_selectorValuationDeficit_eq_zero_of_headPrime
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    (deltaStar betaProt alpha beta : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (p : {p : Nat // p ∈ P}) (hpW : p.1 <= B.sampleData.W)
    (hcompatibility :
      Rhead.target p =
        ((certificate.selectorTailTarget R fixed).factorization p.1 :
          Real)) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta
            (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass))
        p.1 = 0 := by
  dsimp only
  have hmoment :=
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_headTarget
      (K := K) B hprime Rhead I hlo hhi Kphysical hpattern
        R certificate deltaStar betaProt alpha beta hactiveSmooth p hpW
  unfold bankPaperCanonicalSelectorValuationDeficit
  rw [← hcompatibility, hmoment, sub_self]

/-! ## High-prime row reindexing -/











/-! ## WithTop and rounded support wrappers -/

/-- Finite selector-tail support for the literal frozen-top source.  All
high-prime coordinates come from charged row totals.  The only low-prime
compatibility is the displayed reserve/selector-target equality. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_deficitSupportedOnPrimeBand
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hprime : ∀ p ∈ P, p.Prime)
    (Rhead : HeadSimplexReserve P)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Kphysical : PhysicalInterpolationTarget I)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime Rhead.exponent)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hcompatibility : ∀ p : {p : Nat // p ∈ P},
      p.1 <= B.sampleData.W ->
        Rhead.target p =
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real))
    (hprefix : 2 * depth + 1 <= B.sampleData.W)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hrows :
      let T := B.barycentricTargetOfPaperData
        I hlo hhi Rhead Kphysical
      BankPaperCanonicalChargedNonsmoothRowRealization
        (K := K) R certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha beta
              (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass)))
    (hcapacity : forall label,
      IsCompleteRoughLabel (yNat B.sampleData.n) label ->
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          RoughCanonicalPostchargeRowCapacity
            R certificate deltaStar K label) :
    let T := B.barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta
          (bankPaperCanonicalScaledActiveSeed T Rhead.activeMass)) := by
  dsimp only at hrows ⊢
  intro q hqPrime hqNotBand
  by_cases hqW : q <= B.sampleData.W
  · have hqHead : q ∈ primesUpTo B.sampleData.W :=
      mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
    let p : {p : Nat // p ∈ P} := ⟨q, hhead hqHead⟩
    simpa only [p] using
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_selectorValuationDeficit_eq_zero_of_headPrime
        (K := K) B hprime Rhead I hlo hhi Kphysical hpattern
          R certificate (R.paperFixedExceptionalFactors deltaStar)
          deltaStar betaProt alpha beta hactiveSmooth p hqW
            (hcompatibility p hqW))
  · have hWq : B.sampleData.W < q := Nat.lt_of_not_ge hqW
    have hyq : yNat B.sampleData.n < q := by
      by_contra hnotY
      have hqy : q <= yNat B.sampleData.n := Nat.le_of_not_gt hnotY
      exact hqNotBand (mem_primeBand.mpr ⟨hqPrime, hWq, hqy⟩)
    exact
      bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_chargedRows_of_yNat_lt
        (K := K) R certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha beta
              (bankPaperCanonicalScaledActiveSeed
                (B.barycentricTargetOfPaperData
                  I hlo hhi Rhead Kphysical)
                Rhead.activeMass))
          q hyq hrows hcapacity
            (bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
              (W := B.sampleData.W) R certificate deltaStar
                hprefix hqPrime hWq hchargeDvd)



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpRoundedValuationRateConnector -/
section


/-!
# Rounded smooth-source to guarded valuation rate

The sharp common-profile closure controls the unrounded barycentric active
moment against the constant guarded label-one broad layer.  The exact
frozen-top decomposition has one additional term: the same nearest-integer
mass is inserted in each physical copy of the zero head cell.

This file bounds that literal correction directly.  Its cell mass is at most
`1 / 4`, by the universal half-unit nearest-integer error, and reciprocal
zero-cell valuation means then put it on the same
`secondOrderScale / (p * L)` scale.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.FiniteProbability

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## The synchronized guarded active mass -/

/-- The guarded label-one active mass has its pointwise paper-scale upper
bound without an additional analytic hypothesis.  Indeed, its support is
contained in the raw label-one smooth pool, which in turn lies in an
interval of cardinality at most `n`. -/
theorem
    abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real)
    (hn : 1 < n) :
    |bankPaperCanonicalGuardedSmoothBaseMass R certificate
        deltaStar W K betaAct| ≤
      |betaAct| * secondOrderScale n := by
  have hL : 0 < L n := L_pos hn
  have hguardedSubset :
      R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1 ⊆
        bankPaperCanonicalRawSmoothBasePool W n h K := by
    simpa only [bankPaperCanonicalRawSmoothBasePool] using
      R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
        certificate deltaStar W K 1
  have hrawSubset :
      bankPaperCanonicalRawSmoothBasePool W n h K ⊆
        roughBroadLowerBlock n h K := by
    intro a ha
    change a ∈ roughCanonicalBroadCorrectionPool W n h K (yNat n) 1 at ha
    have haRow := mem_completeRoughRowFiber.mp ha
    exact (mem_roughHeadFree.mp haRow.1).1
  have hcardNat :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1).card ≤ n := by
    calc
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card ≤
          (bankPaperCanonicalRawSmoothBasePool W n h K).card :=
        Finset.card_le_card hguardedSubset
      _ ≤ (roughBroadLowerBlock n h K).card :=
        Finset.card_le_card hrawSubset
      _ ≤ n := by
        simp only [roughBroadLowerBlock, Nat.card_Ioc]
        omega
  have hcard :
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1).card : Real) ≤ (n : Real) := by
    exact_mod_cast hcardNat
  have hcardNonneg :
      (0 : Real) ≤
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card : Real) :=
    Nat.cast_nonneg _
  unfold bankPaperCanonicalGuardedSmoothBaseMass
  rw [abs_mul, abs_div, abs_of_pos hL, abs_of_nonneg hcardNonneg]
  rw [secondOrderScale]
  calc
    |betaAct| / L n *
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K 1).card : Real) ≤
        |betaAct| / L n * (n : Real) :=
      mul_le_mul_of_nonneg_left hcard
        (div_nonneg (abs_nonneg _) hL.le)
    _ = |betaAct| * ((n : Real) / L n) := by ring

/-! ## The literal nearest-integer correction -/





/-! ## Sharp rounded finite-rate connector -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineActiveLedgerConnector -/
section


/-!
# Density packaging for the Section 9 active ledger

The weak Section 9 local input asks for one fixed constant `Cactive` such
that every literal baseline coordinate is at most `Cactive / L`.  For the
canonical scaled seed this is already a consequence of three earlier facts:

* its mass family is `O(secondOrderScale)`;
* every guard-deleted canonical cell has a fixed positive linear density;
* every normalized barycentric cell mass is at most one.

This file packages those facts.  The finite lemma exposes the exact
mass/cardinality calculation.  The eventual theorem uses the proved
guarded raw-cell density and takes a genuine finite minimum over all fixed
head/physical cells.  No coordinate bound is assumed.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A common density for every fixed canonical cell -/



/-- The finite density floor is strictly positive. -/
theorem bankPaperCanonicalGuardedCellDensityFloor_pos
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) :
    0 < bankPaperCanonicalGuardedCellDensityFloor Phead I := by
  classical
  let densities := (Finset.univ : Finset (Cell Head)).image
    (fun cell =>
      paperCellDensity (Phead cell.1)
        (I.lower cell.2) (I.upper cell.2) / 4)
  have hdensities : densities.Nonempty :=
    Finset.univ_nonempty.image _
  have hmem :
      bankPaperCanonicalGuardedCellDensityFloor Phead I ∈ densities := by
    exact Finset.min'_mem densities hdensities
  obtain ⟨cell, _hcell, hEq⟩ := Finset.mem_image.mp hmem
  rw [← hEq]
  exact div_pos
    (paperCellDensity_pos (Phead cell.1)
      (I.lower_lt_upper cell.2))
    (by norm_num)

/-- The density floor is below the proved guarded density of each cell. -/
theorem bankPaperCanonicalGuardedCellDensityFloor_le
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PhysicalIntervals) (cell : Cell Head) :
    bankPaperCanonicalGuardedCellDensityFloor Phead I ≤
      paperCellDensity (Phead cell.1)
        (I.lower cell.2) (I.upper cell.2) / 4 := by
  classical
  unfold bankPaperCanonicalGuardedCellDensityFloor
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨cell, Finset.mem_univ cell, rfl⟩)

/-! ## Finite coordinate packaging -/



/-! ## Eventual canonical density wrapper -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPostHfitBalancedAlphaEventually -/
section


/-!
# Eventual feasibility of the canonical Post-Hfit balanced coefficient

The paper first chooses a positive total broad coefficient
`beta < c / (3 * roughHeadDensity W)` and then takes the fixed high-block
multiplicity sufficiently large.  This file records that choice at the
exact finite level.

No quota or height-ledger asymptotic is needed.  The defining ceiling gives

`c * n / log n <= upperTailLength c n`

pointwise, which already makes the numerator of the balanced coefficient
nonnegative.  Taking the multiplicity at least the reciprocal head density
makes the same numerator at most its denominator.
-/

open Filter Set

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperBridgeFit

noncomputable section

/-! ## Finite balanced-coefficient algebra -/

/-- The exact two inequalities behind feasibility of the balanced raw
coefficient.  The hypotheses are deliberately stated before specializing
`h` to the paper's integral upper-tail length. -/
theorem roughHeadBalancedAlpha_mem_Icc_of_tail_lower
    {W n h K : Nat} {c beta ell : Real}
    (hc : 0 < c) (hn : 0 < n) (hKpos : 0 < K)
    (hell : 0 < ell) (hbeta : 0 ≤ beta)
    (hbetaUpper : beta ≤ c / roughHeadDensity W)
    (hKlarge : 1 / roughHeadDensity W ≤ (K : Real))
    (htail : c * (n : Real) / ell ≤ (h : Real)) :
    roughHeadBalancedAlpha W n h K beta ell ∈
      Icc (0 : Real) 1 := by
  have hdensity : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have htailBase : 0 < c * (n : Real) / ell :=
    div_pos (mul_pos hc hnReal) hell
  have hhReal : (0 : Real) < (h : Real) :=
    htailBase.trans_le htail
  have hh : 0 < h := by
    exact_mod_cast hhReal
  have hden :
      0 < (((K * h : Nat) : Real)) := by
    exact_mod_cast Nat.mul_pos hKpos hh
  have hsub :
      (((n - K * h : Nat) : Real)) ≤ (n : Real) := by
    exact_mod_cast Nat.sub_le n (K * h)
  have hbetaDiv : 0 ≤ beta / ell :=
    div_nonneg hbeta hell.le
  have htermNonneg :
      0 ≤ (beta / ell) * (((n - K * h : Nat) : Real)) :=
    mul_nonneg hbetaDiv (Nat.cast_nonneg _)
  have htermUpper :
      (beta / ell) * (((n - K * h : Nat) : Real)) ≤
        (h : Real) / roughHeadDensity W := by
    calc
      (beta / ell) * (((n - K * h : Nat) : Real)) ≤
          (beta / ell) * (n : Real) :=
        mul_le_mul_of_nonneg_left hsub hbetaDiv
      _ = beta * ((n : Real) / ell) := by ring
      _ ≤ (c / roughHeadDensity W) * ((n : Real) / ell) :=
        mul_le_mul_of_nonneg_right hbetaUpper
          (div_nonneg hnReal.le hell.le)
      _ = (c * (n : Real) / ell) / roughHeadDensity W := by ring
      _ ≤ (h : Real) / roughHeadDensity W :=
        div_le_div_of_nonneg_right htail hdensity.le
  have hnumNonneg :
      0 ≤ (h : Real) / roughHeadDensity W -
        (beta / ell) * (((n - K * h : Nat) : Real)) :=
    sub_nonneg.mpr htermUpper
  have hheadUpper :
      (h : Real) / roughHeadDensity W ≤
        (((K * h : Nat) : Real)) := by
    calc
      (h : Real) / roughHeadDensity W =
          (1 / roughHeadDensity W) * (h : Real) := by ring
      _ ≤ (K : Real) * (h : Real) :=
        mul_le_mul_of_nonneg_right hKlarge hhReal.le
      _ = (((K * h : Nat) : Real)) := by
        norm_num only [Nat.cast_mul]
  constructor
  · rw [roughHeadBalancedAlpha]
    exact div_nonneg hnumNonneg hden.le
  · rw [roughHeadBalancedAlpha]
    exact
      (div_le_one hden).2
        ((sub_le_self _ htermNonneg).trans hheadUpper)

namespace BankPaperRealization

/-! ## Canonical bridge specialization -/

/-- Pointwise feasibility for the literal Post-Hfit coefficient.  The only
scale input is the paper's exact upper-tail ceiling. -/
theorem bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBounds
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {c : Real} (K0 : Nat)
    (betaProt betaAct : Real) (hc : 0 < c)
    (hbeta : 0 ≤ betaProt + betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤
        c / roughHeadDensity B.sampleData.W)
    (hKlarge :
      1 / roughHeadDensity B.sampleData.W ≤
        (((K0 + 1 : Nat) : Real))) :
    bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  have htail :
      c * (B.sampleData.n : Real) / B.L ≤
        (upperTailLength c B.sampleData.n : Real) := by
    calc
      c * (B.sampleData.n : Real) / B.L =
          c * secondOrderScale B.sampleData.n := by
        unfold BridgeData.L secondOrderScale
        ring
      _ ≤ (upperTailLength c B.sampleData.n : Real) := by
        simpa only [upperTailLength] using
          (Nat.le_ceil
            (c * secondOrderScale B.sampleData.n))
  simpa only [bankPaperCanonicalPostHfitBalancedAlpha] using
    (roughHeadBalancedAlpha_mem_Icc_of_tail_lower
      (W := B.sampleData.W) (n := B.sampleData.n)
      (h := upperTailLength c B.sampleData.n) (K := K0 + 1)
      (c := c) (beta := betaProt + betaAct) (ell := B.L)
      hc (Nat.zero_lt_of_lt B.n_gt_one) (by omega)
      B.L_pos hbeta hbetaUpper hKlarge htail)

/-- Uniform family form used by the Section 9 supplier.  It applies to every
bridge with the synchronized width, hence in particular to the coherent
canonical/post-height bridge family. -/
theorem eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (W K0 : Nat) {c betaProt betaAct : Real} (hc : 0 < c)
    (hbeta : 0 ≤ betaProt + betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real))) :
    ∀ᶠ n : Nat in atTop,
      ∀ B : BridgeData Head Band,
        B.sampleData.n = n →
        B.sampleData.W = W →
        bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  refine Eventually.of_forall ?_
  intro n B _hBn hBW
  apply
    bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBounds
      B K0 betaProt betaAct hc hbeta
  · simpa only [hBW] using hbetaUpper
  · simpa only [hBW] using hKlarge





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceResidualConnector -/
section


/-!
# The coherent post-height source residual

This file closes the three primitive residual fields for the literal
pre-rounding frozen-top source, once the source target has been honestly
constructed from paper head and physical data.

The target interface is deliberately transparent.  It asks for the exact
equalities

* `Tsource = B.barycentricTargetOfPaperData ... Rhead Kphysical`, and
* `qTilde = Rhead.activeMass`,

together with the certificate-derived head-target compatibility.  It does
not store feasibility, charged rows, selector support, a source state, or
the residual conclusion in an input structure.

All remaining inputs are primitive geometry and synchronization facts.
The coordinate capacity is derived from the guarded canonical cell-density
theorem and the literal guarded smooth-mass estimate.  Nonsmooth endpoint
slack, charged-row realization, and postcharge row capacity are supplied by
their existing assumption-free eventual theorems.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Two reusable capacity facts -/

/-- A paper-scale mass bound and a linear lower bound for every sample cell
give the exact `Cactive / L` bound for the scaled source seed itself.

Unlike the active-ledger wrapper, this statement does not identify the
scaled seed with the bridge baseline; the post-height bridge has a different
active mass, so that identification would be false for `Tsource,qTilde`. -/
theorem bankPaperCanonical_scaledActiveSeed_le_divLog_of_cellDensity
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (T : BarycentricTarget B.sampleData)
    (q Cq density : Real)
    (hCq : 0 <= Cq) (hdensity : 0 < density)
    (hq : |q| <= Cq * secondOrderScale B.sampleData.n)
    (hcard : forall cell : Cell Head,
      density * (B.sampleData.n : Real) <=
        (Fintype.card (B.sampleData.SampleAt cell) : Real)) :
    forall m : B.sampleData.Sample,
      bankPaperCanonicalScaledActiveSeed T q m <=
        (Cq / density) / B.L := by
  intro m
  let cell := B.sampleData.cellOf m
  have hcardPos :
      0 < (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos cell
  have hcellPos : 0 < T.baseline.cellMass cell :=
    T.baseline.cellMass_pos cell
  have hcellOne : T.baseline.cellMass cell <= 1 :=
    bankPaperCanonical_baseline_cellMass_le_one T cell
  have hscaled :
      bankPaperCanonicalScaledActiveSeed T q m =
        (q * T.baseline.cellMass cell) /
          Fintype.card (B.sampleData.SampleAt cell) := by
    unfold bankPaperCanonicalScaledActiveSeed BaselineAllocation.baseWeight
    change
      q * (T.baseline.cellMass cell /
          Fintype.card (B.sampleData.SampleAt cell)) =
        (q * T.baseline.cellMass cell) /
          Fintype.card (B.sampleData.SampleAt cell)
    ring
  have hscaledUpper :
      bankPaperCanonicalScaledActiveSeed T q m <=
        |q| / Fintype.card (B.sampleData.SampleAt cell) := by
    rw [hscaled]
    calc
      (q * T.baseline.cellMass cell) /
            Fintype.card (B.sampleData.SampleAt cell) <=
          (|q| * T.baseline.cellMass cell) /
            Fintype.card (B.sampleData.SampleAt cell) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self q) hcellPos.le)
          hcardPos.le
      _ <= (|q| * 1) /
            Fintype.card (B.sampleData.SampleAt cell) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcellOne (abs_nonneg q))
          hcardPos.le
      _ = |q| / Fintype.card (B.sampleData.SampleAt cell) := by
        ring
  have hmassUpper :
      |q| / Fintype.card (B.sampleData.SampleAt cell) <=
        (Cq * secondOrderScale B.sampleData.n) /
          Fintype.card (B.sampleData.SampleAt cell) :=
    div_le_div_of_nonneg_right hq hcardPos.le
  have hfactorNonneg : 0 <= (Cq / density) / B.L :=
    div_nonneg (div_nonneg hCq hdensity.le) B.L_pos.le
  have hcardScaled :=
    mul_le_mul_of_nonneg_left (hcard cell) hfactorNonneg
  have hscaleIdentity :
      Cq * secondOrderScale B.sampleData.n =
        ((Cq / density) / B.L) *
          (density * (B.sampleData.n : Real)) := by
    change
      Cq * ((B.sampleData.n : Real) / B.L) =
        ((Cq / density) / B.L) *
          (density * (B.sampleData.n : Real))
    field_simp [hdensity.ne', B.L_pos.ne']
  have hcapacity :
      (Cq * secondOrderScale B.sampleData.n) /
            Fintype.card (B.sampleData.SampleAt cell) <=
        (Cq / density) / B.L := by
    apply (div_le_iff₀ hcardPos).2
    calc
      Cq * secondOrderScale B.sampleData.n =
          ((Cq / density) / B.L) *
            (density * (B.sampleData.n : Real)) :=
        hscaleIdentity
      _ <= ((Cq / density) / B.L) *
            (Fintype.card (B.sampleData.SampleAt cell) : Real) :=
        hcardScaled
  exact hscaledUpper.trans (hmassUpper.trans hcapacity)

/-- Eventual linear cell capacity for every bridge whose structured sample
is literally the canonical guard-deleted sample.  This is the cardinality
part of the active-ledger theorem, exposed independently because the source
seed is not the post-height bridge baseline. -/
theorem eventually_bankPaperCanonical_canonicalSample_cellDensityFloor
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (Phead : Head -> Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData Head Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell : Cell Head,
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
            forall cell : Cell Head,
              bankPaperCanonicalGuardedCellDensityFloor Phead I *
                  (B.sampleData.n : Real) <=
                (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
  have hguardedDensity :=
    eventually_guarded_rawCell_density Phead I Cprom Cbank ledger
  filter_upwards [hguardedDensity, eventually_gt_atTop 0] with
      n hguardedDensityN hn
  intro B hBn hsep hremaining hcanonical cell
  have hnReal : 0 < (n : Real) := by
    exact_mod_cast hn
  have hcellFinset :
      B.sampleData.cellFinset cell =
        rawCell Phead I n cell \ (ledger n).guards := by
    calc
      B.sampleData.cellFinset cell =
          (canonicalSampleData (W := B.sampleData.W)
            Phead I (ledger B.sampleData.n)
              hsep hremaining).cellFinset cell :=
        congrArg
          (fun D : StructuredSampleData Head => D.cellFinset cell)
          hcanonical
      _ = rawCell Phead I B.sampleData.n cell \
          (ledger B.sampleData.n).guards :=
        canonicalSampleData_cellFinset
          Phead I (ledger B.sampleData.n) hsep hremaining cell
      _ = rawCell Phead I n cell \ (ledger n).guards := by
        rw [hBn]
  have hcardEq :
      (Fintype.card (B.sampleData.SampleAt cell) : Real) =
        ((rawCell Phead I n cell \ (ledger n).guards).card : Real) := by
    rw [Fintype.card_coe, hcellFinset]
  have hdensityLe :
      bankPaperCanonicalGuardedCellDensityFloor Phead I <=
        paperCellDensity (Phead cell.1)
          (I.lower cell.2) (I.upper cell.2) / 4 :=
    bankPaperCanonicalGuardedCellDensityFloor_le Phead I cell
  calc
    bankPaperCanonicalGuardedCellDensityFloor Phead I *
          (B.sampleData.n : Real) =
        bankPaperCanonicalGuardedCellDensityFloor Phead I *
          (n : Real) := by rw [hBn]
    _ <=
        (paperCellDensity (Phead cell.1)
          (I.lower cell.2) (I.upper cell.2) / 4) * (n : Real) :=
      mul_le_mul_of_nonneg_right hdensityLe hnReal.le
    _ = paperCellDensity (Phead cell.1)
          (I.lower cell.2) (I.upper cell.2) * (n : Real) / 4 := by
      ring
    _ <= ((rawCell Phead I n cell \
        (ledger n).guards).card : Real) :=
      hguardedDensityN cell
    _ = (Fintype.card
        (B.sampleData.SampleAt cell) : Real) :=
      hcardEq.symm

/-! ## Eventual residual construction -/

/-- The strongest noncircular eventual constructor for the literal
frozen-top source residual.

The paper target is supplied by its actual constructors and exact
equalities, rather than by an unconstrained target contract.  Feasibility,
charged rows, and full prime-band support are conclusions.  The source
target `T`, mass `qTilde`, realization, certificate, fixed exceptional set,
and rough level `K0 + 1` are unchanged in the result. -/
theorem
    eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Patterns : PaperHeadSimplex.Tag P -> Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : forall n, Ledger n Cprom Cbank)
    (depth W K0 : Nat)
    {c deltaStar betaProt betaAct sigma : Real}
    (hc : 0 < c) (hdeltaStar : 0 < deltaStar)
    (hbetaProt : 0 <= betaProt) (hbetaAct : 0 < betaAct)
    (hsigmaNonneg : 0 <= sigma) (hsigmaProt : sigma <= betaProt)
    (hbetaUpper :
      betaProt + betaAct <= c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W <= (((K0 + 1 : Nat) : Real)))
    (hprefix : 2 * depth + 1 <= W) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        forall
          (hcanonicalSep :
            physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell : Cell (PaperHeadSimplex.Tag P),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Patterns I (G B.sampleData.n)
                  hcanonicalSep hremaining ->
        forall
          (R : BankPaperRealization B.sampleData.n
            (upperEndpoint B.sampleData.n
              (upperTailLength c B.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth
            B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth))
          (T : BarycentricTarget B.sampleData)
          (qTilde : Real),
          qTilde =
              bankPaperCanonicalGuardedSmoothBaseMass R certificate
                deltaStar B.sampleData.W (K0 + 1) betaAct ->
        forall
          (hprime : ∀ p ∈ P, p.Prime)
          (Rhead : HeadSimplexReserve P)
          (Kphysical : PhysicalInterpolationTarget I)
          (hlo : forall sign, B.sampleData.lo sign =
            physicalBound (I.lower sign) B.sampleData.n)
          (hhi : forall sign, B.sampleData.hi sign =
            physicalBound (I.upper sign) B.sampleData.n),
          T =
              B.barycentricTargetOfPaperData
                I hlo hhi Rhead Kphysical ->
          qTilde = Rhead.activeMass ->
          B.sampleData.pattern =
              PaperHeadSimplex.pattern P hprime Rhead.exponent ->
          primesUpTo B.sampleData.W ⊆ P ->
          B.sampleData.HeadPatternsSeparated ->
          (forall sign, 1 <= I.lower sign) ->
          (forall sign, I.upper sign <= 2) ->
          (forall sign,
            physicalBound (I.upper sign) B.sampleData.n <=
              2 * B.sampleData.n -
                (K0 + 1) * upperTailLength c B.sampleData.n) ->
          (K0 + 1) * upperTailLength c B.sampleData.n <=
              B.sampleData.n ->
          (forall m : B.sampleData.Sample,
            B.sampleData.value m ∉
              R.roughCanonicalGuardSet certificate deltaStar) ->
          (forall p : {p : Nat // p ∈ P},
            p.1 <= B.sampleData.W ->
              Rhead.target p =
                ((certificate.selectorTailTarget R
                  (R.paperFixedExceptionalFactors deltaStar)).factorization
                    p.1 : Real)) ->
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
              certificate.prechargedTailTarget ->
          BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
            (K := K0 + 1) B R certificate
              (R.paperFixedExceptionalFactors deltaStar)
              T deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                (betaProt + betaAct) qTilde := by
  let density :=
    bankPaperCanonicalGuardedCellDensityFloor Patterns I
  let Cactive := |betaAct| / density
  have hdensity : 0 < density := by
    simpa only [density] using
      bankPaperCanonicalGuardedCellDensityFloor_pos Patterns I
  have hCactive : 0 <= Cactive := by
    dsimp only [Cactive]
    exact div_nonneg (abs_nonneg betaAct) hdensity.le
  have hbetaNonneg : 0 <= betaProt + betaAct :=
    add_nonneg hbetaProt hbetaAct.le
  have Halpha :=
    eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
      (Head := PaperHeadSimplex.Tag P) (Band := Band)
      W K0 hc hbetaNonneg hbetaUpper hKlarge
  have Hnonsmooth :=
    eventually_roughCanonicalBalancedNonsmoothBounds
      W K0 hc hdeltaStar hbetaAct hsigmaProt
  have Hrows :=
    eventually_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_chargedNonsmoothRows
      (P := P) (Band := Band) depth W (K0 + 1) hc hdeltaStar
  have Hcapacity :=
    BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
      W (K0 + 1) 1 hc hdeltaStar
  have HcellDensity :=
    eventually_bankPaperCanonical_canonicalSample_cellDensityFloor
      (Band := Band) Patterns I Cprom Cbank G
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have HsourceRoom :
      ∀ᶠ n : Nat in atTop, betaProt + Cactive <= L n :=
    hLTop.eventually (eventually_ge_atTop (betaProt + Cactive))
  have HbetaRoom :
      ∀ᶠ n : Nat in atTop, betaProt + betaAct <= L n :=
    hLTop.eventually (eventually_ge_atTop (betaProt + betaAct))
  filter_upwards [
      Halpha, Hnonsmooth, Hrows, Hcapacity, HcellDensity,
      HsourceRoom, HbetaRoom,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_yNat_lt_centralAnchorCutoff depth]
      with n halphaN hnonsmoothN hrowsN hcapacityN hcellDensityN
        hsourceRoomN hbetaRoomN hnCutoff hyCutoff
  intro B hBn hBW hcanonicalSep hremaining hcanonical
    R certificate T qTilde hmass
    hprime Rhead Kphysical hlo hhi hT hqTarget hpattern hhead
    hheadSeparated hlowerOne hupperTwo hupperBroad hroughDepth
    houtsideGuard hcompatibility hchargeDvd
  subst n
  have halpha :
      bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct ∈ Set.Icc (0 : Real) 1 :=
    halphaN B rfl hBW
  have hactiveBroad :
      forall m : B.sampleData.Sample,
        B.sampleData.value m ∈
          roughBroadLowerBlock B.sampleData.n
            (upperTailLength c B.sampleData.n) (K0 + 1) := by
    intro m
    exact
      bankPaperCanonicalStructuredValue_mem_roughBroadLowerBlock_of_physicalIntervals
        B I (upperTailLength c B.sampleData.n) (K0 + 1)
          hlowerOne hupperTwo hlo hhi hupperBroad m
  have hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow
          certificate deltaStar (K0 + 1) 1 :=
    bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
      B R certificate deltaStar I hlowerOne hupperTwo hlo hhi
        hroughDepth houtsideGuard
  have hqBound :
      |qTilde| <= |betaAct| * secondOrderScale B.sampleData.n := by
    calc
      |qTilde| =
          |bankPaperCanonicalGuardedSmoothBaseMass R certificate
            deltaStar B.sampleData.W (K0 + 1) betaAct| :=
        congrArg abs hmass
      _ <= |betaAct| * secondOrderScale B.sampleData.n :=
        abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
          R certificate deltaStar B.sampleData.W (K0 + 1)
            betaAct B.n_gt_one
  have hcard :
      forall cell : Cell (PaperHeadSimplex.Tag P),
        density * (B.sampleData.n : Real) <=
          (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
    simpa only [density] using
      hcellDensityN B rfl hcanonicalSep hremaining hcanonical
  have hseedUpper :
      forall m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T qTilde m <=
          Cactive / B.L := by
    simpa only [Cactive] using
      bankPaperCanonical_scaledActiveSeed_le_divLog_of_cellDensity
        B T qTilde |betaAct| density (abs_nonneg betaAct)
          hdensity hqBound hcard
  have hsourceRoom : betaProt + Cactive <= B.L := by
    simpa only [BridgeData.L] using hsourceRoomN
  have hbetaRoom : betaProt + betaAct <= B.L := by
    simpa only [BridgeData.L] using hbetaRoomN
  have hbetaBox :
      0 <= (betaProt + betaAct) / B.L ∧
        (betaProt + betaAct) / B.L <= 1 := by
    constructor
    · exact div_nonneg hbetaNonneg B.L_pos.le
    · apply (div_le_iff₀ B.L_pos).2
      simpa only [one_mul] using hbetaRoom
  have hsigmaBox : 0 <= sigma / B.L :=
    div_nonneg hsigmaNonneg B.L_pos.le
  have hnonsmooth :=
    hnonsmoothN depth R certificate hnCutoff hyCutoff
  have hfloor :
      forall label,
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          sigma / B.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar B.sampleData.W (K0 + 1) label
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  (betaProt + betaAct) B.L| <=
            (betaProt + betaAct) / B.L := by
    intro label hlabel
    simpa only [
      bankPaperCanonicalPostHfitBalancedAlpha, BridgeData.L, hBW] using
      (hnonsmooth label hlabel).1
  have hceiling :
      forall label,
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          (betaProt + betaAct) / B.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar B.sampleData.W (K0 + 1) label
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  (betaProt + betaAct) B.L| <=
            1 - sigma / B.L := by
    intro label hlabel
    simpa only [
      bankPaperCanonicalPostHfitBalancedAlpha, BridgeData.L, hBW] using
      (hnonsmooth label hlabel).2
  have hqNonneg : 0 <= qTilde := by
    rw [hqTarget]
    exact Rhead.activeMass_pos.le
  have hfeasible :=
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_scaledSeedDivLog_of_twoSidedSlack
      (K := K0 + 1) B R certificate T deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) qTilde sigma Cactive
        hqNonneg halpha hbetaProt hbetaBox hsigmaBox
        hheadSeparated hactiveBroad hCactive hseedUpper
        hsourceRoom hfloor hceiling
  have hrows :=
    hrowsN B rfl hBW R certificate T betaProt
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) qTilde
  have hpostchargeCapacity :
      forall label,
        IsCompleteRoughLabel (yNat B.sampleData.n) label ->
          RoughCanonicalActiveNonexceptionalLabel
              B.sampleData.n deltaStar label ->
            RoughCanonicalPostchargeRowCapacity
              R certificate deltaStar (K0 + 1) label := by
    intro label hcomplete hactive
    exact
      (hcapacityN depth R.anchorGuardLeftCore R.anchorGuardRightCore
        (R.centralChangedMarkers depth) R certificate hnCutoff hyCutoff
          label hcomplete hactive).2.2
  have hrowsTarget :
      let Tpaper :=
        B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical
      BankPaperCanonicalChargedNonsmoothRowRealization
        (K := K0 + 1) R certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
            (K := K0 + 1) B R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct)
              (bankPaperCanonicalScaledActiveSeed
                Tpaper Rhead.activeMass)) := by
    dsimp only
    rw [← hT, ← hqTarget]
    exact hrows
  have hprefixB : 2 * depth + 1 <= B.sampleData.W := by
    simpa only [hBW] using hprefix
  have hsupportTarget :=
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_deficitSupportedOnPrimeBand
      (K := K0 + 1) B hprime Rhead I hlo hhi Kphysical hpattern
        R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) hactiveSmooth hhead hcompatibility
          hprefixB hchargeDvd hrowsTarget hpostchargeCapacity
  have hsupport :
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
        (W := B.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet
          certificate deltaStar (K0 + 1))
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            (betaProt + betaAct)
            (bankPaperCanonicalScaledActiveSeed T qTilde)) := by
    rw [hT, hqTarget]
    exact hsupportTarget
  exact ⟨hfeasible, hrows, hsupport⟩

end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal004_014.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget
