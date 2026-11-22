-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.512235+00:00
-- url     : https://prove2.me/submissions/bb007b0f-049e-4204-b40f-374231d1b58e

import Definitions.Def_erdos390_remaining_analytic_propositions_007
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_canonical
import Theorems.Thm_Erdos390_WholePaper_eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact



section
theorem Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower : Erdos390.RemainingAnalyticGoal008_004 := @Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact
end
section
universe u_1
theorem Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs : Erdos390.RemainingAnalyticGoal004_013.{u_1} := @Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs_compact
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

/- Source module: Erdos390.WholePaper.ResidualCentralFactors -/
section


/-! # The finite family of promoted residual central factors -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section











theorem residualCentralPrimes_exponent_pos {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) :
    0 < (Nat.choose (2 * n) n).factorization p := by
  have hpMem : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hp).1
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  exact (Nat.prime_of_mem_primeFactors hpMem).factorization_pos_of_dvd
    hchoosePos.ne' (Nat.dvd_of_mem_primeFactors hpMem)









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPrimeBlockDecomposition -/
section


/-!
# Exact low/high decomposition of the central binomial coefficient

The central binomial coefficient is the product of its complete prime-power
blocks.  Splitting those blocks at the anchor cutoff and promoting every low
block therefore introduces exactly one aggregate power of two and no other
valuation error.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem largeCentralPrimes_prime {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem largeCentralPrimes_gt {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : X < p :=
  (Finset.mem_filter.mp hp).2











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.UpperScale -/
section


/-!
# Elementary scale facts for the upper bound

This module isolates the exact ceiling and endpoint used on the upper-bound
side of the paper.  Every asymptotic statement is proved directly from
elementary real-logarithm limits.  No prime-counting input is used.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section





/-- The elementary logarithmic comparison `log n / n → 0`, made public
for later upper-bound estimates. -/
theorem log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

/-- The second-order scale `n / log n` diverges to infinity. -/
theorem secondOrderScale_tendsto_atTop :
    Tendsto secondOrderScale atTop atTop := by
  have hpos :
      ∀ᶠ n : ℕ in atTop,
        0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright :
      Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨log_natCast_div_natCast_tendsto_zero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    change (Real.log (n : ℝ) / (n : ℝ))⁻¹ =
      secondOrderScale n
    rw [secondOrderScale, inv_div]

/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

/-- Eventually the second-order scale is strictly positive. -/
theorem eventually_secondOrderScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < secondOrderScale n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact secondOrderScale_pos hn

/-- The second-order scale is sublinear. -/
theorem secondOrderScale_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ secondOrderScale n / (n : ℝ))
      atTop (nhds 0) := by
  have hinvLog :
      Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ))
        atTop (nhds 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  apply hinvLog.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [secondOrderScale]
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  have hlogNe : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp





/-- Ceiling changes `c n/log n` only by a negligible relative error. -/
theorem upperTailLength_normalized_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailLength c n : ℝ) / secondOrderScale n)
      atTop (nhds c) := by
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc.le).comp
      secondOrderScale_tendsto_atTop

/-- The chosen upper tail is `o(n)`. -/
theorem upperTailLength_ratio_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hmul :=
    (upperTailLength_normalized_tendsto hc).mul
      secondOrderScale_ratio_tendsto_zero
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hscaleNe : secondOrderScale n ≠ 0 := hscale.ne'
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  field_simp





















end

end Erdos390.WholePaper

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightLedger -/
section


/-!
# The exact smooth-row quota and height ledger from Section 8

This file records the algebraic part of the paper's smooth-row initialization
without replacing any actual finite mass by an asymptotic main term.

The literal active base component is the constant weight `betaAct / L n` on
the head-free, `yNat n`-smooth part of the broad interval.  Its exact support
is the complete-rough row with label one.  The later definitions follow the
paper verbatim:

* `Q_sm(0)` is the nearest integer to `m_sm,fr + qTilde`, with a half-integer
  tie sent to the smaller integer;
* `q0 = Q_sm(0) - m_sm,fr`;
* `Q_sm(d) = Q_sm(0) - d` and `qAct(d) = q0 - d`;
* `A0 = logY - Lambda0 - q0 * L` and `A(d) = A0 + d * L`;
* `d` is the tie-lower nearest integer to
  `(mu * q0 - A0) / (L + mu)`.

All displayed identities and the two nearest-integer errors are unconditional.
The analytic comparison between the raw base mass and the actual post-guard
mass is deliberately left to the companion asymptotic module.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal rough smooth base component -/

















/-! ## Tie-lower nearest integers -/









/-- The universal half-unit rounding error. -/
theorem bankPaperNearestIntegerTieLower_abs_sub_le (x : Real) :
    |(bankPaperNearestIntegerTieLower x : Real) - x| ≤ 1 / 2 := by
  have hcell :=
    (bankPaperNearestIntegerTieLower_eq_iff x
      (bankPaperNearestIntegerTieLower x)).1 rfl
  apply abs_le.mpr
  constructor <;> linarith

/-! ## Exact smooth-row quota initialization -/







/-- Exact expression for the initialization error. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_sub_actual
    (mFrozen qTilde : Real) :
    bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde =
      (bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
        (mFrozen + qTilde) := by
  unfold bankPaperCanonicalSmoothInitialActiveMass
  ring

/-- The paper's literal bound `|q0 - qTilde| <= 1/2`. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen qTilde : Real) :
    |bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde| ≤
      1 / 2 := by
  rw [bankPaperCanonicalSmoothInitialActiveMass_sub_actual]
  exact bankPaperNearestIntegerTieLower_abs_sub_le (mFrozen + qTilde)

















/-! ## Exact frozen-height ledger and centered adjustment -/











/-- The rounded height adjustment is within one half of `dStar`. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
    (n : Nat) (mu q0 A0 : Real) :
    |(bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real) -
        bankPaperCanonicalSmoothHeightCenter n mu q0 A0| ≤ 1 / 2 :=
  bankPaperNearestIntegerTieLower_abs_sub_le
    (bankPaperCanonicalSmoothHeightCenter n mu q0 A0)















/-! ## Literal Section 8 families -/



















/-- Family-level half-unit initialization error. -/
theorem bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
    (mFrozen qTilde : Nat -> Real) (n : Nat) :
    |bankPaperCanonicalSmoothQ0Family mFrozen qTilde n - qTilde n| <=
      1 / 2 :=
  bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen n) (qTilde n)





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

/-- Every fixed exceptional factor is a literal upper-tail occurrence. -/
theorem paperFixedExceptionalFactors_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  simpa only [roughUpperBlock, upperEndpoint] using
    R.paperFixedExceptionalFactors_subset_upperBlock deltaStar



















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











/-! ## The literal three-coordinate local census -/





/-! ## Guarded broad-pool and postcharge capacities -/







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



/-- The fixed Dickman floor is strictly positive. -/
theorem roughCanonicalPoolDickmanFloor_pos :
    0 < roughCanonicalPoolDickmanFloor := by
  unfold roughCanonicalPoolDickmanFloor
  exact rho_pos_on_zero_five (by norm_num) le_rfl



/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/



/-- The retained raw broad-pool density is strictly positive. -/
theorem roughCanonicalRawBroadPoolDensity_pos (W : Nat) :
    0 < roughCanonicalRawBroadPoolDensity W := by
  unfold roughCanonicalRawBroadPoolDensity
  exact div_pos
    (mul_pos (roughHeadDensity_pos W)
      roughCanonicalPoolDickmanFloor_pos) (by norm_num)









/-! ## Uniform paper-scale choices -/























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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalHeadActiveMassEventually -/
section


/-!
# Eventual lower bound for the paper's head-reserve active mass

The paper obtains its final active mass from the exact ledger

`q^{act}(d) = q₀ - d`,

where the rough smooth active mass satisfies `q₀ ≍ n / log n` and the
height-centering change satisfies `d = O(n / log² n)`.  Only the lower
half of that comparison is needed to prove the constructor hypothesis
`1 <= q^{act}(d)` for all sufficiently large `n`.

The repository's `HeadSimplexReserve` currently stores only
`0 < activeMass`.  It has no family constructor, no connection to the
rough smooth active mass, and no asymptotic lower-bound field.  This file
therefore isolates the exact missing paper input as a positive lower
multiple of `secondOrderScale n = n / log n`.  Everything after that input
is proved here:

* the active mass tends to infinity and eventually exceeds every constant;
* in particular it is eventually at least one;
* an `o(n / log n)` height change preserves a fixed positive lower multiple;
* the paper's stronger `O(n / log² n)` change is automatically little-o;
* the canonical scaled seed has eventual mass at least one and its
  self-selector satisfies the full actual-active-measure constructor.

A concrete reserve of mass `1 / 2` is also constructed.  It proves that
strict positivity alone cannot imply the desired inequality, so the
repository needs an additional growth input until the missing
rough-active-mass construction is connected to `HeadSimplexReserve`.
The predicate below is exactly the lower half of the growth statement
used in the paper.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

/-! ## The irreducible paper-scale input -/





/-! ## Positivity is genuinely insufficient -/









/-! ## All eventual consequences of the minimal input -/

/-- A fixed positive multiple of `n / log n` tends to infinity, hence so
does any active mass lying eventually above it. -/
theorem bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    Tendsto q atTop atTop := by
  rcases H with ⟨c, hc, hq⟩
  have hscale : Tendsto
      (fun n : Nat => c * secondOrderScale n) atTop atTop :=
    secondOrderScale_tendsto_atTop.const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ hscale
  exact hq

/-- Every fixed real threshold is eventually below the active mass. -/
theorem eventually_const_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) (C : Real) :
    ∀ᶠ n : Nat in atTop, C <= q n :=
  (bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower q H).eventually
    (eventually_ge_atTop C)

/-- The exact constructor threshold follows with `C = 1`. -/
theorem eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    ∀ᶠ n : Nat in atTop, 1 <= q n :=
  eventually_const_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    q H 1





/-! ## The exact `q₀-d` height-centering algebra -/

/-- The paper's error scale `n / log² n` is little-o of
`secondOrderScale n = n / log n`. -/
theorem secondOrderScale_div_L_isLittleO_secondOrderScale :
    (fun n : Nat => secondOrderScale n / L n) =o[atTop]
      secondOrderScale := by
  have hzero : ∀ᶠ n : Nat in atTop,
      secondOrderScale n = 0 -> secondOrderScale n / L n = 0 :=
    Eventually.of_forall fun n hn => by simp [hn]
  apply (isLittleO_iff_tendsto' hzero).mpr
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : Nat => (L n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hLTop
  apply hinv.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hL : 0 < L n := L_pos hn
  field_simp [hscale.ne', hL.ne']

/-- Subtracting a little-o height-centering change from a macroscopically
positive base mass preserves half of its lower constant. -/
theorem bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
    (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =o[atTop] secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) := by
  rcases Hq0 with ⟨c, hc, hq0⟩
  refine ⟨c / 2, half_pos hc, ?_⟩
  have hdBound := hd.bound (half_pos hc)
  filter_upwards [hq0, hdBound, eventually_secondOrderScale_pos]
      with n hq0n hdn hscale
  have hdn' : |d n| <= (c / 2) * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscale] using hdn
  have hdle : d n <= (c / 2) * secondOrderScale n :=
    (le_abs_self (d n)).trans hdn'
  calc
    (c / 2) * secondOrderScale n =
        c * secondOrderScale n -
          (c / 2) * secondOrderScale n := by ring
    _ <= q0 n - (c / 2) * secondOrderScale n :=
      sub_le_sub_right hq0n _
    _ <= q0 n - d n := sub_le_sub_left hdle _

/-- This is the paper's displayed implication: a base mass bounded below
on the `n / log n` scale and a change of order `n / log² n` yield a final
active mass with the required positive paper-scale lower bound. -/
theorem bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
    (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =O[atTop]
      (fun n : Nat => secondOrderScale n / L n)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) := by
  apply bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
    q0 d Hq0
  exact hd.trans_isLittleO
    secondOrderScale_div_L_isLittleO_secondOrderScale





/-! ## Literal scaled seeds and actual-measure constructors -/







/-! ## The literal paper-head specialization -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic -/
section


/-!
# The analytic Section 8 smooth-row quota and height bridge

The raw active smooth component from the exact companion file has a positive
`n / log n` lower bound by the repository's uniform de Bruijn--Saias and
fixed-head estimates.  This file proves that bound directly for complete-
rough label one, then propagates it through the exact nearest-integer and
height-center constructions.

Only one repository-level analytic ledger remains absent.  It is named
`BankPaperCanonicalSectionEightAnalyticLedger` below and contains exactly:

* the actual post-guard smooth mass differs from the explicit raw base mass
  by `o(n / log n)`;
* the literal frozen height defect `A0` is `O(n / log n)`.

These are precisely the two estimates asserted together in the paper's
Section 8 frozen ledger.  No selector, active-measure, or positivity premise
is hidden in that predicate.  Every consequence after it, including
`d = O(n / log^2 n)` and the positive lower bound for `q0 - d`, is proved
here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The label-one raw base pool is macroscopically large -/







/-- Therefore the literal `betaAct / L` base component has the minimal
positive paper-scale lower bound whenever `betaAct > 0`. -/
theorem bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    (W K : Nat) {c betaAct : Real} (hc : 0 < c) (hbeta : 0 < betaAct) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct) := by
  use betaAct * roughCanonicalRawBroadPoolDensity W,
    mul_pos hbeta (roughCanonicalRawBroadPoolDensity_pos W)
  have hpool :=
    eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower W K hc
  filter_upwards [hpool, eventually_gt_atTop 1] with n hpoolN hn
  have hL : 0 < L n := L_pos hn
  calc
    (betaAct * roughCanonicalRawBroadPoolDensity W) * secondOrderScale n =
        (betaAct / L n) *
          (roughCanonicalRawBroadPoolDensity W * (n : Real)) := by
      unfold secondOrderScale L
      ring
    _ <= (betaAct / L n) *
          ((bankPaperCanonicalRawSmoothBasePool W n
            (upperTailLength c n) K).card : Real) :=
      mul_le_mul_of_nonneg_left hpoolN (div_nonneg hbeta.le hL.le)
    _ = bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) K betaAct := by
      rfl

/-- The raw base mass is also `O(n / log n)`, by the elementary containment
of its support in the broad interval. -/
theorem bankPaperCanonicalRawSmoothBaseMass_isBigO
    (W K : Nat) (c betaAct : Real) :
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct) =O[atTop] secondOrderScale := by
  apply (isBigO_iff).2
  use |betaAct|
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hscale : 0 < secondOrderScale n := secondOrderScale_pos (by omega)
  have hsubset : bankPaperCanonicalRawSmoothBasePool W n
      (upperTailLength c n) K ⊆
        roughBroadLowerBlock n (upperTailLength c n) K := by
    intro a ha
    change a ∈ roughCanonicalBroadCorrectionPool W n
      (upperTailLength c n) K (yNat n) 1 at ha
    have haRow := mem_completeRoughRowFiber.mp ha
    exact (mem_roughHeadFree.mp haRow.1).1
  have hcardNat :
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card <= n := by
    calc
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card <=
          (roughBroadLowerBlock n (upperTailLength c n) K).card :=
        Finset.card_le_card hsubset
      _ <= n := by
        simp only [roughBroadLowerBlock, Nat.card_Ioc]
        omega
  have hcard :
      ((bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card : Real) <= (n : Real) := by
    exact_mod_cast hcardNat
  have hcardNonneg :
      (0 : Real) <=
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) :=
    Nat.cast_nonneg _
  rw [bankPaperCanonicalRawSmoothBaseMass, Real.norm_eq_abs,
    abs_mul, abs_div, abs_of_pos hL, abs_of_nonneg hcardNonneg,
    Real.norm_eq_abs, abs_of_pos hscale]
  rw [secondOrderScale]
  have hcoef : 0 <= |betaAct| / L n :=
    div_nonneg (abs_nonneg _) hL.le
  calc
    |betaAct| / L n *
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) <=
        |betaAct| / L n * (n : Real) :=
      mul_le_mul_of_nonneg_left hcard hcoef
    _ = |betaAct| * ((n : Real) / L n) := by ring

/-! ## The exact missing analytic ledger -/



/-! ## Nearest-integer initialization preserves the paper scale -/

/-- The uniformly bounded initialization error is little-o of
`secondOrderScale`. -/
theorem bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
    (mFrozen qTilde : Nat -> Real) :
    (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
      qTilde n) =o[atTop] secondOrderScale := by
  have hbounded :
      (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
        qTilde n) =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply (isBigO_iff).2
    use 1 / 2
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
        mFrozen qTilde n
  have hnorm : Tendsto (norm ∘ secondOrderScale) atTop atTop := by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using
      tendsto_abs_atTop_atTop.comp secondOrderScale_tendsto_atTop
  have hone : (fun _n : Nat => (1 : Real)) =o[atTop]
      secondOrderScale :=
    isLittleO_const_left.mpr (Or.inr hnorm)
  exact hbounded.trans_isLittleO hone

/-- A negligible raw-to-post-guard loss transfers the positive lower bound
from the explicit raw base mass to the actual mass `qTilde`. -/
theorem bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (rawBase qTilde : Nat -> Real)
    (Hraw : BankPaperCanonicalActiveMassPaperScaleLower rawBase)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower qTilde := by
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
      rawBase (fun n => rawBase n - qTilde n) Hraw Hguard with
    ⟨C, hC, hlower⟩
  use C, hC
  filter_upwards [hlower] with n hn
  convert hn using 1 ; ring

/-- The half-unit nearest-integer initialization transfers that lower bound
from `qTilde` to the literal `q0` family. -/
theorem bankPaperCanonicalSmoothQ0Family_paperScaleLower
    (mFrozen qTilde : Nat -> Real)
    (HqTilde : BankPaperCanonicalActiveMassPaperScaleLower qTilde) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  have hd : (fun n => qTilde n -
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde n) =o[atTop]
        secondOrderScale :=
    hround.neg_left.congr_left (fun n => by ring)
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
      qTilde
      (fun n => qTilde n -
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
      HqTilde hd with ⟨C, hC, hlower⟩
  use C, hC
  filter_upwards [hlower] with n hn
  convert hn using 1 ; ring

/-- A little-o raw-to-post-guard error also transfers the upper `O(N)`
bound. -/
theorem bankPaperCanonicalPostGuardSmoothMass_isBigO
    (rawBase qTilde : Nat -> Real)
    (Hraw : rawBase =O[atTop] secondOrderScale)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    qTilde =O[atTop] secondOrderScale := by
  exact (Hraw.sub Hguard.isBigO).congr_left (fun n => by ring)

/-- The nearest-integer `q0` family inherits the upper `O(N)` bound. -/
theorem bankPaperCanonicalSmoothQ0Family_isBigO
    (mFrozen qTilde : Nat -> Real)
    (HqTilde : qTilde =O[atTop] secondOrderScale) :
    bankPaperCanonicalSmoothQ0Family mFrozen qTilde =O[atTop]
      secondOrderScale := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  exact (HqTilde.add hround.isBigO).congr_left (fun n => by ring)

/-! ## The logarithmically smaller height adjustment -/

/-- The paper's scale `n / log^2 n` tends to infinity. -/
theorem secondOrderScale_div_L_tendsto_atTop :
    Tendsto (fun n : Nat => secondOrderScale n / L n) atTop atTop := by
  have hzero : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (nhds 0) := by
    simpa only [L, Function.comp_apply, id_eq] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  have hpos : ∀ᶠ n : Nat in atTop,
      0 < L n ^ 2 / (n : Real) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (pow_pos (L_pos hn) 2) (by positivity)
  have hright : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hnReal : (n : Real) ≠ 0 := by positivity
  apply (eq_div_iff hL.ne').2
  change (L n ^ 2 / (n : Real))⁻¹ * L n = (n : Real) / L n
  rw [inv_div]
  field_simp [hL.ne', hnReal]

/-- The reciprocal of `L + mu` is `O(1/L)` for fixed positive `mu`. -/
theorem bankPaperCanonical_inv_L_add_mu_isBigO_inv_L
    {mu : Real} (hmu : 0 < mu) :
    (fun n : Nat => (L n + mu)⁻¹) =O[atTop]
      (fun n : Nat => (L n)⁻¹) := by
  apply (isBigO_iff).2
  use 1
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hdenom : 0 < L n + mu := add_pos hL hmu
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdenom),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), one_mul]
  exact (inv_le_inv₀ hdenom hL).2 (le_add_of_nonneg_right hmu.le)

/-- From `q0 = O(N)` and `A0 = O(N)`, the exact rounded height adjustment
constructed in the companion file satisfies `d = O(N/L)`. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_isBigO
    {mu : Real} (hmu : 0 < mu) (q0 A0 : Nat -> Real)
    (Hq0 : q0 =O[atTop] secondOrderScale)
    (HA0 : A0 =O[atTop] secondOrderScale) :
    (fun n => (bankPaperCanonicalSmoothHeightAdjustment
      n mu (q0 n) (A0 n) : Real)) =O[atTop]
        (fun n => secondOrderScale n / L n) := by
  have hnum : (fun n => mu * q0 n - A0 n) =O[atTop]
      secondOrderScale :=
    (Hq0.const_mul_left mu).sub HA0
  have hinv := bankPaperCanonical_inv_L_add_mu_isBigO_inv_L hmu
  have hcenter : (fun n => bankPaperCanonicalSmoothHeightCenter
      n mu (q0 n) (A0 n)) =O[atTop]
        (fun n => secondOrderScale n / L n) := by
    apply (hnum.mul hinv).congr
    · intro n
      rw [bankPaperCanonicalSmoothHeightCenter, div_eq_mul_inv]
    · intro n
      rw [div_eq_mul_inv]
  have hroundOne :
      (fun n => (bankPaperCanonicalSmoothHeightAdjustment
          n mu (q0 n) (A0 n) : Real) -
        bankPaperCanonicalSmoothHeightCenter n mu (q0 n) (A0 n))
        =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply (isBigO_iff).2
    use 1 / 2
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
        n mu (q0 n) (A0 n)
  have hone : (fun _n : Nat => (1 : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
    apply (isBigO_iff).2
    use 1
    have hlarge := secondOrderScale_div_L_tendsto_atTop.eventually
      (eventually_ge_atTop (1 : Real))
    filter_upwards [hlarge] with n hn
    have hnonneg : 0 <= secondOrderScale n / L n := zero_le_one.trans hn
    simpa only [norm_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg hnonneg] using hn
  have hround := hroundOne.trans hone
  exact (hcenter.add hround).congr_left (fun n => by ring)

/-! ## Full propagation from the minimal missing ledger -/

/-- Under the single missing Section 8 analytic ledger, the literal `q0`
family has a positive paper-scale lower bound. -/
theorem bankPaperCanonicalSectionEight_q0_paperScaleLower
    (W K : Nat) {c betaAct : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) := by
  have hraw := bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    W K hc hbeta
  have hpost := bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    qTilde hraw Hledger.1
  exact bankPaperCanonicalSmoothQ0Family_paperScaleLower
    mFrozen qTilde hpost

/-- The same ledger gives the paper's displayed `d = O(n/log^2 n)`. -/
theorem bankPaperCanonicalSectionEight_d_isBigO
    (W K : Nat) (c betaAct : Real) {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSmoothDRealFamily
        mu logY Lambda0 mFrozen qTilde =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  have hrawBigO := bankPaperCanonicalRawSmoothBaseMass_isBigO
    W K c betaAct
  have hpostBigO := bankPaperCanonicalPostGuardSmoothMass_isBigO
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    qTilde hrawBigO Hledger.1
  have hq0BigO := bankPaperCanonicalSmoothQ0Family_isBigO
    mFrozen qTilde hpostBigO
  simpa only [bankPaperCanonicalSmoothDRealFamily,
      bankPaperCanonicalSmoothDIntFamily] using
    bankPaperCanonicalSmoothHeightAdjustment_isBigO hmu
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde)
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)
      hq0BigO Hledger.2

/-- Consequently the constructed final active mass `qAct(d) = q0 - d`
retains a positive `n / log n` lower bound. -/
theorem bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde) := by
  have hq0 := bankPaperCanonicalSectionEight_q0_paperScaleLower
    W K hc hbeta logY Lambda0 mFrozen qTilde Hledger
  have hd := bankPaperCanonicalSectionEight_d_isBigO
    W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  exact bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde)
    (bankPaperCanonicalSmoothDRealFamily
      mu logY Lambda0 mFrozen qTilde) hq0 hd



/-- The exact active-measure constructor threshold follows eventually. -/
theorem eventually_one_le_bankPaperCanonicalSectionEight_finalActiveMass
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      1 <= bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde n :=
  eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (bankPaperCanonicalSmoothFinalActiveMassFamily
      mu logY Lambda0 mFrozen qTilde)
    (bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
      W K hc hbeta hmu logY Lambda0 mFrozen qTilde Hledger)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellProducerConnector -/
section


/-!
# Concrete producer and mass choice for the two zero-head cells

This file isolates the two finite facts needed by the structured
prebridge producer.

First, a sample in the zero head cell is coprime to the complete head
modulus.  Hence it belongs to the guarded broad correction pool as soon as
its physical interval lies below the literal broad cutoff and every sample
value is known pointwise to avoid the canonical guard set.  In particular, no
cardinality surplus theorem is used to prove membership.

Second, the height adjustment has a canonical symmetric realization: put
`-d / 2` in each of the two physical zero-head cells.  Its total change is
the integer `-d`, and the exact lower and upper coordinate-capacity
conditions reduce to two scalar inequalities involving the old total cell
mass and the guard-deleted cell cardinality.

The nearest-integer normalization from `qTilde` to `q0` is recorded
separately.  That first change is generally real rather than integral; the
integer prebridge ledger applies to the subsequent height change from
`q0` to `q0 - d`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums

noncomputable section

namespace BankPaperRealization

/-! ## The fixed physical intervals eventually lie below the broad cutoff -/

/-- A fixed endpoint strictly below `2` eventually leaves enough room for
the whole `K * upperTailLength` top strip.  This is the literal numerical
inequality used in the paper to put the upper physical pool below
`2n-Kh`. -/
theorem eventually_physicalBound_le_two_mul_sub_upperTailLength
    (K : Nat) {c b : Real} (hc : 0 < c) (hb0 : 0 <= b) (hbTwo : b < 2) :
    ∀ᶠ n : Nat in atTop,
      physicalBound b n <= 2 * n - K * upperTailLength c n := by
  have htailEvent : ∀ᶠ n : Nat in atTop,
      (((K * upperTailLength c n : Nat) : Real) / (n : Real)) < 2 - b := by
    have hT := (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
    have hzeroLt : (K : Real) * 0 < 2 - b := by
      simpa using sub_pos.mpr hbTwo
    have hsmall := hT.eventually
      (eventually_lt_nhds hzeroLt)
    filter_upwards [hsmall] with n hn
    have hn' :
        (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) < 2 - b := hn
    simpa [Nat.cast_mul, mul_div_assoc] using hn'
  filter_upwards [htailEvent, eventually_gt_atTop 0] with n htail hn
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have htailCross :
      ((K * upperTailLength c n : Nat) : Real) <
        (2 - b) * (n : Real) :=
    (div_lt_iff₀ hnReal).mp htail
  have hfloor :
      (physicalBound b n : Real) <= b * (n : Real) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hb0 (by positivity))
  have hsumReal :
      (physicalBound b n : Real) +
          (K * upperTailLength c n : Nat) < 2 * (n : Real) := by
    calc
      (physicalBound b n : Real) +
          (K * upperTailLength c n : Nat) <=
        b * (n : Real) + (K * upperTailLength c n : Nat) :=
          add_le_add hfloor le_rfl
      _ < 2 * (n : Real) := by nlinarith
  have hsumNat :
      physicalBound b n + K * upperTailLength c n <= 2 * n := by
    exact_mod_cast hsumReal.le
  omega

/-- Simultaneous two-sign form for the paper's fixed physical intervals. -/
theorem eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
    (I : PhysicalIntervals) (K : Nat) {c : Real} (hc : 0 < c)
    (hupperStrict : forall sigma, I.upper sigma < 2) :
    ∀ᶠ n : Nat in atTop, forall sigma,
      physicalBound (I.upper sigma) n <=
        2 * n - K * upperTailLength c n := by
  have hminus :=
    eventually_physicalBound_le_two_mul_sub_upperTailLength K hc
      (le_of_lt ((I.lower_pos .minus).trans (I.lower_lt_upper .minus)))
      (hupperStrict .minus)
  have hplus :=
    eventually_physicalBound_le_two_mul_sub_upperTailLength K hc
      (le_of_lt ((I.lower_pos .plus).trans (I.lower_lt_upper .plus)))
      (hupperStrict .plus)
  filter_upwards [hminus, hplus] with n hnMinus hnPlus
  intro sigma
  cases sigma with
  | minus => exact hnMinus
  | plus => exact hnPlus

/-! ## The zero head pattern produces head-freeness -/









/-! ## Canonical symmetric mass choices -/















/-! ## Exact finite coordinate capacity -/















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalBridgeRelevantGuardLedger -/
section


/-!
# The bridge-relevant numerical-guard ledger

The literal rough construction uses the global five-family guard

`anchors ∪ fixedExceptional ∪ donors ∪ baseState ∪ alternateState`.

That global set is not the guard census used by the smooth bridge.  Fixed
exceptional factors and donors lie above `2n`, while the two bank endpoint
states have a prime complete-rough label above `yNat n`.  Hence, on the
positive `yNat n`-smooth values at most `2n` which occur in every bridge
cell, the global guard agrees exactly with the promoted residual anchors
whose base prime is at most `yNat n`.

This file makes that relevant guard literal.  Its cardinality is at most
`yNat n`, so it fits in the promoted part of `GuardSlot`.  We adjoin the
harmless sentinel value `0` before enumerating it.  This avoids a false
nonemptiness requirement on an image of a nonempty slot type; the sentinel
cannot occur in a structured cell.  Two promoted slots per smooth integer
therefore suffice uniformly, and no bank slot is required.

Thus the correct replacement for a global
`ledger.guards = roughCanonicalGuardSet` hypothesis is the eventual local
predicate `BankPaperCanonicalBridgeGuardAgreement`.  A total fixed ledger
family, chosen before any realization or certificate, uses a harmless
zero-valued fallback on the finite prefix where the relevant guard does not
fit.  Once a realization exists the paper census forces the canonical branch,
so this fixed family agrees with the global rough guard on the bridge
universe.  The concrete elimination interfaces below give equality after
deleting guards from a raw cell, equality after restricting deletion to
structured active values, and pointwise avoidance of the full guard.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Enumerating an arbitrary finite guard together with a zero sentinel -/





/-- The padded enumeration has exactly the requested guard together with
the sentinel; no other integer is introduced. -/
theorem ledgerOfFinsetWithZero_guards
    {n Cprom Cbank : Nat} (guards : Finset Nat)
    (hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n Cprom Cbank)) :
    (ledgerOfFinsetWithZero guards hcard).guards = insert 0 guards := by
  classical
  let e : (insert 0 guards : Finset Nat) ↪
      GuardSlot n Cprom Cbank :=
    guardFinsetWithZeroEmbedding guards hcard
  change Finset.univ.image
      (Function.extend e
        (fun a : (insert 0 guards : Finset Nat) => a.1)
        (fun _ => 0)) =
    insert 0 guards
  ext a
  constructor
  · intro ha
    rw [Finset.mem_image] at ha
    obtain ⟨slot, _hslot, rfl⟩ := ha
    by_cases hslot : ∃ x, e x = slot
    · rw [Function.extend_def, dif_pos hslot]
      exact (Classical.choose hslot).property
    · rw [Function.extend_apply'
        (g := fun x : (insert 0 guards : Finset Nat) => x.1)
        (e' := fun _ : GuardSlot n Cprom Cbank => 0)
        slot hslot]
      exact Finset.mem_insert_self 0 guards
  · intro ha
    rw [Finset.mem_image]
    refine ⟨e ⟨a, ha⟩, Finset.mem_univ _, ?_⟩
    simpa only using
      e.injective.extend_apply
        (fun x : (insert 0 guards : Finset Nat) => x.1)
        (fun _ : GuardSlot n Cprom Cbank => 0)
        ⟨a, ha⟩

/-! ## The literal bridge-relevant subfamily -/





/-- Every relevant promoted anchor belongs to the certificate's full anchor
set. -/
theorem roughCanonicalBridgeRelevantGuardSet_subset_anchors
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    roughCanonicalBridgeRelevantGuardSet certificate ⊆
      certificate.anchors := by
  intro a ha
  rw [roughCanonicalBridgeRelevantGuardSet,
    bankPaperCanonicalSmoothResidualAnchorPool,
    Finset.mem_image] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  rw [certificate.anchors_eq, fullCentralAnchors]
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr
    ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩

/-- A smooth guarded central anchor is necessarily one of the relevant
promoted residual anchors.  Large routed anchors retain their marker prime
above the smooth cutoff. -/
theorem guardedCentralAnchor_mem_bridgeRelevant_of_smooth
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    {a : Nat} (ha : a ∈ certificate.anchors) (haPos : 0 < a)
    (haSmooth : a ∈ Nat.smoothNumbers (yNat n + 1)) :
    a ∈ roughCanonicalBridgeRelevantGuardSet certificate := by
  have haLabel : completeRoughLabel (yNat n) a = 1 :=
    (completeRoughLabel_eq_one_iff_mem_smoothNumbers haPos).mpr haSmooth
  rw [certificate.anchors_eq, fullCentralAnchors] at ha
  rcases Finset.mem_union.mp ha with haPromoted | haLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haPromoted
    rw [roughCanonicalBridgeRelevantGuardSet,
      bankPaperCanonicalSmoothResidualAnchorPool]
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
    by_contra hpNotLe
    have hpHigh : yNat n < p := Nat.lt_of_not_ge hpNotLe
    have hpPrime := residualCentralPrimes_prime hp
    have hpDvdFactor : p ∣ promotedCentralFactor n p := by
      unfold promotedCentralFactor promotedBlock centralPrimeBlock
      exact dvd_mul_of_dvd_right
        (dvd_pow_self p
          (residualCentralPrimes_exponent_pos hp).ne') _
    have hpDvdLabel :
        p ∣ completeRoughLabel (yNat n)
          (promotedCentralFactor n p) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hpPrime hpHigh
        haPos.ne' hpDvdFactor
    rw [haLabel] at hpDvdLabel
    exact hpPrime.not_dvd_one hpDvdLabel
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp haLarge
    have hPPrime := largeCentralPrimes_prime hP
    have hPHigh : yNat n < P :=
      hyCutoff.trans (largeCentralPrimes_gt hP)
    have hPDvdLabel :
        P ∣ completeRoughLabel (yNat n)
          (largeCentralAnchor certificate.q P) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
        haPos.ne' (dvd_mul_right P (certificate.q P))
    rw [haLabel] at hPDvdLabel
    exact (hPPrime.not_dvd_one hPDvdLabel).elim



namespace BankPaperRealization

/-- On every positive smooth integer at most `2n`, membership in the
bridge-relevant guard is equivalent to membership in the global five-family
rough guard. -/
theorem mem_roughCanonicalBridgeRelevantGuardSet_iff_mem_guardSet
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    {a : Nat} (haPos : 0 < a) (haUpper : a <= 2 * n)
    (haSmooth : a ∈ Nat.smoothNumbers (yNat n + 1)) :
    a ∈ roughCanonicalBridgeRelevantGuardSet certificate ↔
      a ∈ R.roughCanonicalGuardSet certificate deltaStar := by
  classical
  constructor
  · intro ha
    have haAnchor :=
      roughCanonicalBridgeRelevantGuardSet_subset_anchors certificate ha
    simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
      Finset.mem_union]
    exact Or.inl <| Or.inl <| Or.inl <| Or.inl haAnchor
  · intro haGuard
    have haLabel : completeRoughLabel (yNat n) a = 1 :=
      (completeRoughLabel_eq_one_iff_mem_smoothNumbers haPos).mpr haSmooth
    simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
      Finset.mem_union] at haGuard
    rcases haGuard with
      (((haAnchor | haFixed) | haDonor) | haBase) | haAlternate
    · exact guardedCentralAnchor_mem_bridgeRelevant_of_smooth
        certificate hyCutoff haAnchor haPos haSmooth
    · have haTail :=
        R.paperFixedExceptionalFactors_subset_tail deltaStar haFixed
      exact (Nat.not_lt_of_ge haUpper (Finset.mem_Ioc.mp haTail).1).elim
    · have haTail := R.prechargeDonorSet_subset_tail haDonor
      exact (Nat.not_lt_of_ge haUpper (Finset.mem_Ioc.mp haTail).1).elim
    · rw [prechargeBaseState, indexedPathState, Finset.mem_image] at haBase
      obtain ⟨request, _hrequest, rfl⟩ := haBase
      rw [R.prechargeBase_completeRoughLabel_eq_marker] at haLabel
      have hmarker := R.yNat_lt_paperMarker request
      have hySix := R.six_le_yNat
      omega
    · rw [prechargeAlternateState, indexedPathState,
        Finset.mem_image] at haAlternate
      obtain ⟨request, _hrequest, rfl⟩ := haAlternate
      rw [R.prechargeAlternate_completeRoughLabel_eq_marker] at haLabel
      have hmarker := R.yNat_lt_paperMarker request
      have hySix := R.six_le_yNat
      omega

/-! ## The canonical two-promoted-slot ledger -/





/-- Whenever a realization exists, its pointwise canonical relevant ledger is
the fixed family chosen before the realization and certificate.  The
realization supplies only the proof that the canonical branch of the total
family is active. -/
theorem roughCanonicalBridgeRelevantLedgerFamily_eq
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    roughCanonicalBridgeRelevantLedgerFamily depth n =
      R.roughCanonicalBridgeRelevantLedger certificate := by
  have hcard :
      (insert 0
        (bankPaperCanonicalSmoothResidualAnchorPool n
          (centralAnchorCutoff depth n) (yNat n))).card <=
        Fintype.card (GuardSlot n 2 0) := by
    simpa only [roughCanonicalBridgeRelevantGuardSet] using
      R.roughCanonicalBridgeRelevantGuardSet_insert_zero_card_le_guardSlot
        certificate
  unfold roughCanonicalBridgeRelevantLedgerFamily
  rw [dif_pos hcard]
  unfold roughCanonicalBridgeRelevantLedger
    roughCanonicalBridgeRelevantGuardSet
  rfl

/-- Exact image of the canonical relevant ledger. -/
theorem roughCanonicalBridgeRelevantLedger_guards
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    (R.roughCanonicalBridgeRelevantLedger certificate).guards =
      insert 0 (roughCanonicalBridgeRelevantGuardSet certificate) := by
  unfold roughCanonicalBridgeRelevantLedger
  apply ledgerOfFinsetWithZero_guards



/-- The canonical relevant ledger satisfies the local agreement interface. -/
theorem roughCanonicalBridgeRelevantLedger_agreement
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    BankPaperCanonicalBridgeGuardAgreement
      (R.roughCanonicalBridgeRelevantLedger certificate)
      R certificate deltaStar := by
  intro a haPos haUpper haSmooth
  rw [R.roughCanonicalBridgeRelevantLedger_guards certificate,
    Finset.mem_insert]
  have haZero : a ≠ 0 := haPos.ne'
  simp only [haZero, false_or]
  exact R.mem_roughCanonicalBridgeRelevantGuardSet_iff_mem_guardSet
    certificate deltaStar hyCutoff haPos haUpper haSmooth

/-- Finite local agreement for the fixed ledger family. -/
theorem roughCanonicalBridgeRelevantLedgerFamily_agreement
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    BankPaperCanonicalBridgeGuardAgreement
      (roughCanonicalBridgeRelevantLedgerFamily depth n)
      R certificate deltaStar := by
  rw [R.roughCanonicalBridgeRelevantLedgerFamily_eq certificate]
  exact R.roughCanonicalBridgeRelevantLedger_agreement
    certificate deltaStar hyCutoff



/-- Eventual agreement with the ledger family fixed before quantifying over
the realization and certificate.  This is the quantifier order consumed by
the canonical structured-sample and one-shot bridge interfaces. -/
theorem eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
    {c : Real} (depth : Nat) (deltaStar : Real) :
    ∀ᶠ n : Nat in atTop,
      forall
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
        BankPaperCanonicalBridgeGuardAgreement
          (roughCanonicalBridgeRelevantLedgerFamily depth n)
          R certificate deltaStar := by
  filter_upwards [eventually_yNat_lt_centralAnchorCutoff depth] with
    n hyCutoff
  intro R certificate
  exact R.roughCanonicalBridgeRelevantLedgerFamily_agreement
    certificate deltaStar hyCutoff

/-! ## Equality on raw cells and structured active values -/













end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector -/
section


/-!
# One-shot Section 8 orchestration for the two zero-head cells

This file joins the three already audited layers of the literal Section 8
construction:

* the analytic ledger gives the `q0` and integer-height asymptotics;
* the two-zero-cell producer realizes the height change by `-d / 2` in
  each physical copy of the zero head cell; and
* the structured prebridge ledger transports the resulting integral row
  change and the exact head-prime moments.

The source selector is not postulated through a new interface.  It is the
canonical protected-plus-ambient selector, and its finite selector state is
read directly from the existing
`BankPaperCanonicalRoundedSelectorTangentInput`.  Consequently the only
new feasibility work is at the two coordinates that actually change.

The terminal eventual theorem uses the same `hcanonical` and
`cellMassMargin` arguments as the canonical Proposition 8.7 statement.  It
only assumes that the ledger and rough guard agree on the positive, smooth,
at-most-`2n` structured universe.  Together with the canonical sample guards,
this yields pointwise exclusion from the full rough guard without any global
Finset equality.  To invoke the existing actual P87 endpoint consumer after
the structured placement, one must additionally identify
the rebalanced seed with a bridge baseline (`Hmeasure` and `hseed`) and
supply the existing analytic `Hfit`; those are retained under their
existing names rather than hidden in a new assumption package.
-/

open Filter Topology Asymptotics Set
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

/-! ## A reusable two-cell scalar capacity lemma -/



/-! ## Height-only capacity from the Section 8 ledger -/









/-! ## Reusing the rounded source selector -/







/-! ## Exact quota transport -/











/-! ## Canonical P87-local one-shot orchestration -/

/-- A fixed multiple of the upper-tail length is eventually at most the
ambient sample size. -/
theorem eventually_mul_upperTailLength_le_self
    (K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      K * upperTailLength c n <= n := by
  have hT : Tendsto
      (fun n : Nat => (K : Real) *
        ((upperTailLength c n : Real) / (n : Real)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
  have hsmall := hT.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnPos
  have hn' :
      (K : Real) *
          ((upperTailLength c n : Real) / (n : Real)) < 1 := hn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hnPos
  have hnDiv :
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) < 1 := by
    calc
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) =
          (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) := by ring
      _ < 1 := hn'
  have hcross :
      (K : Real) * (upperTailLength c n : Real) < (n : Real) := by
    simpa only [one_mul] using (div_lt_iff₀ hnReal).mp hnDiv
  have hcast :
      ((K * upperTailLength c n : Nat) : Real) < (n : Real) := by
    push_cast
    exact hcross
  exact_mod_cast hcast.le







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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceInputAssemblyConnector -/
section


/-!
# Mechanical source-input assembly for the fresh post-height bridge

This file is downstream from the honest reduction boundary in
`BankPaperCanonicalSectionNinePostHeightEventualSupplierConnector`.  It does
not alter that boundary and does not assert a final supplier.

There are two results.

* A finite constructor takes one already-chosen fresh bridge `J`, its
  genuinely target-dependent synchronization facts, and one already-produced
  rounded source state.  Canonical sample geometry and the two literal
  capacity divisibilities then construct
  `BankPaperCanonicalSectionNinePostHeightSourceInputsAt` and the existing
  `BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt`.
* A mesh-uniform eventual wrapper supplies all of the mechanical hypotheses
  of that finite constructor from the existing Section 8 ledger, canonical
  guarded-cell estimates, bridge-guard agreement, and the rounded-source
  theorem.  The realization and certificate are the literal fiber of the
  same `BankPaperCanonicalGuardedTailFamily`.

The wrapper still quantifies over `J` and assumes the four target-margin
bounds, the exact frozen/final-mass synchronization, and
`BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt`.  Thus it is an
assembly theorem, not a renamed solution of the target/source producer gap.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.FiniteProbability
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Finite assembly -/



/-! ## Eventual mechanical wrapper -/

/-- Uniformly assemble the source package after a coherent fresh bridge has
been chosen on the literal fiber of `F`.

The returned constants `Cmass` and `density` are fixed before the mesh and
before the bridge at an eventual index.  The capacity premise is a plain
conjunction, matching the output shape of the combined-charge tail chooser:
the base-bank divisibility and target-tail identity are derived internally.

This theorem deliberately remains universally quantified over `J` and over
its target/residual facts. -/
theorem
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual
    (P : Finset Nat)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : ∀ sign, 1 ≤ I.lower sign)
    (hupperStrict : ∀ sign, I.upper sign < 2)
    {c : Real} (depth W K0 Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    {deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor : Real}
    (hc : 0 < c) (hbetaAct : 0 < betaAct) (hmu : 0 < mu)
    (hbetaProt : 0 ≤ betaProt)
    (hsourceMarginFloor : 0 < sourceMarginFloor)
    (hheadMarginFloor : 0 < headMarginFloor)
    (hphysicalEtaFloor : 0 < physicalEtaFloor)
    (hpostMarginFloor : 0 < postMarginFloor)
    (hhead : primesUpTo W ⊆ P)
    (logY Lambda0 mFrozen : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar))) :
    ∃ Cmass density : Real,
      0 < Cmass ∧
      0 < density ∧
      ∀ {delta eta : Real}
        (M : RegularRelativeMesh.Mesh delta eta),
        ∀ᶠ n : Nat in atTop,
          ∀ (hdelta : 0 < delta)
          (Bsource : BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M)),
          Bsource.sampleData.n = n →
          Bsource.sampleData.W = W →
          ∀ (hnTail : Ntail ≤ Bsource.sampleData.n),
            let R := F.realization Bsource.sampleData.n hnTail
            let certificate := F.certificate Bsource.sampleData.n hnTail
            ∀ (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                (K0 := K0) M Bsource R certificate I deltaStar hdelta),
              J.exponent = E →
              J.betaProt = betaProt →
              J.betaAct = betaAct →
              (∀
                (hsep :
                  physicalBound (I.upper .minus)
                      J.postHeightBridge.sampleData.n <
                    physicalBound (I.lower .plus)
                      J.postHeightBridge.sampleData.n)
                (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
                  (rawCell (PaperHeadSimplex.pattern P hprime E) I
                      J.postHeightBridge.sampleData.n cell \
                    (roughCanonicalBridgeRelevantLedgerFamily depth
                      J.postHeightBridge.sampleData.n).guards).Nonempty),
                J.postHeightBridge.sampleData =
                    canonicalSampleData
                      (W := J.postHeightBridge.sampleData.W)
                      (PaperHeadSimplex.pattern P hprime E) I
                      (roughCanonicalBridgeRelevantLedgerFamily depth
                        J.postHeightBridge.sampleData.n)
                      hsep hremaining →
                J.qTilde =
                    bankPaperCanonicalGuardedSmoothBaseMass
                      R certificate deltaStar
                        J.postHeightBridge.sampleData.W
                        (K0 + 1) J.betaAct →
                sourceMarginFloor ≤ J.Tsource.cellMassMargin →
                headMarginFloor ≤ J.targetInputs.headMargin →
                physicalEtaFloor ≤ J.targetInputs.physicalEta →
                postMarginFloor ≤ J.postHeightTarget.cellMassMargin →
                mFrozen Bsource.sampleData.n =
                    bankPaperCanonicalTopFrozenSmoothFrozenMass
                      (K := K0 + 1) J.postHeightBridge R certificate
                      deltaStar J.betaProt J.alpha →
                J.qn =
                    bankPaperCanonicalSmoothFinalActiveMassFamily
                      mu logY Lambda0 mFrozen
                        (F.extendedGuardedSmoothBaseMass
                          W (K0 + 1) betaAct deltaStar)
                        Bsource.sampleData.n →
                BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
                    (K := K0 + 1) J.postHeightBridge R certificate
                      (R.paperFixedExceptionalFactors deltaStar)
                      J.Tsource deltaStar J.betaProt J.alpha J.beta
                        J.qTilde →
                (centralAnchorDivisor J.postHeightBridge.sampleData.n
                        (centralAnchorCutoff depth
                          J.postHeightBridge.sampleData.n)
                        certificate.q * R.prechargeBaseStateProduct ∣
                    centralTailProduct J.postHeightBridge.sampleData.n
                      (upperTailLength c
                        J.postHeightBridge.sampleData.n)) ∧
                  R.selectorTailCharge
                        (R.paperFixedExceptionalFactors deltaStar) ∣
                    certificate.prechargedTailTarget →
                ∃ S :
                    BankPaperCanonicalSectionNinePostHeightSourceInputsAt
                      M Bsource R certificate I deltaStar hdelta J,
                  ∃ _Hgap :
                      BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
                        M Bsource R certificate I E deltaStar mu
                          sourceMarginFloor headMarginFloor physicalEtaFloor
                          postMarginFloor logY Lambda0 mFrozen
                          (F.extendedGuardedSmoothBaseMass
                            W (K0 + 1) betaAct deltaStar)
                          hdelta J S,
                    S.Cmass = Cmass ∧ S.density = density) := by
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass W (K0 + 1) betaAct deltaStar
  have Hledger' :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde) := by
    simpa only [qTilde] using Hledger
  have Hraw :
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct) =O[atTop]
        secondOrderScale :=
    bankPaperCanonicalRawSmoothBaseMass_isBigO
      W (K0 + 1) c betaAct
  have HqTilde : qTilde =O[atTop] secondOrderScale :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) (K0 + 1) betaAct)
      qTilde Hraw Hledger'.1
  have Hq0 :
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde =O[atTop]
        secondOrderScale :=
    bankPaperCanonicalSmoothQ0Family_isBigO
      mFrozen qTilde HqTilde
  have Hd :
      bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde =O[atTop]
        (fun n => secondOrderScale n / L n) :=
    bankPaperCanonicalSectionEight_d_isBigO
      W (K0 + 1) c betaAct hmu logY Lambda0 mFrozen qTilde Hledger'
  have HdScale :
      bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde =O[atTop]
        secondOrderScale :=
    Hd.trans secondOrderScale_div_L_isLittleO_secondOrderScale.isBigO
  have Hfinal :
      bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde =O[atTop]
        secondOrderScale :=
    (Hq0.sub HdScale).congr_left fun n => by
      rfl
  obtain ⟨Cmass, hCmass, hmassBound⟩ :=
    (isBigO_iff').mp Hfinal
  let density : Real :=
    bankPaperCanonicalGuardedCellDensityFloor
      (PaperHeadSimplex.pattern P hprime E) I
  have hdensity : 0 < density := by
    simpa only [density] using
      bankPaperCanonicalGuardedCellDensityFloor_pos
        (PaperHeadSimplex.pattern P hprime E) I
  have hupperBroad :=
    eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
      I (K0 + 1) hc hupperStrict
  have hroughDepth :=
    eventually_mul_upperTailLength_le_self (K0 + 1) hc
  have hqnOne :=
    eventually_one_le_bankPaperCanonicalSectionEight_finalActiveMass
      W (K0 + 1) hc hbetaAct hmu
        logY Lambda0 mFrozen qTilde Hledger'
  have hguardAgreement :=
    eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
      (c := c) depth deltaStar
  have hrawDensity :=
    eventually_guarded_rawCell_density
      (PaperHeadSimplex.pattern P hprime E) I
      2 0 (roughCanonicalBridgeRelevantLedgerFamily depth)
  refine ⟨Cmass, density, hCmass, hdensity, ?_⟩
  intro delta eta M
  have hsource :=
    eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs
      (Band := BankPaperCanonicalExponentBand M)
      (deltaStar := deltaStar)
      hprime E hE I hlowerOne hupperStrict
      2 0 (roughCanonicalBridgeRelevantLedgerFamily depth)
      depth W (K0 + 1) hc hbetaAct hsourceMarginFloor hbetaProt
      hhead mFrozen qTilde
      (bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde)
      Hledger'
  filter_upwards [
      hsource, hupperBroad, hroughDepth, hqnOne,
      hguardAgreement, hrawDensity, hmassBound,
      eventually_secondOrderScale_pos]
      with n hsourceN hupperBroadN hroughDepthN hqnOneN
        hguardAgreementN hrawDensityN hmassBoundN hscaleN
  intro hdelta Bsource hBn hBW hnTail
  subst n
  let R := F.realization Bsource.sampleData.n hnTail
  let certificate := F.certificate Bsource.sampleData.n hnTail
  dsimp only
  intro J hexponentSync hbetaProtSync hbetaActSync
    hsep hremaining hcanonical hqTildeActual
    hsourceMargin hheadMargin hphysicalEta hpostMargin
    hmFrozen hfinalActiveMass hsourceResidual hcapacity
  have hBWpost :
      J.postHeightBridge.sampleData.W = W := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hBW
  have hqTildeFiber :
      qTilde Bsource.sampleData.n =
        bankPaperCanonicalGuardedSmoothBaseMass
          R certificate deltaStar W (K0 + 1) betaAct := by
    simp only [
      qTilde,
      BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
      dif_pos hnTail, R, certificate]
  have hqTildeFamily :
      J.qTilde = qTilde Bsource.sampleData.n := by
    calc
      J.qTilde =
          bankPaperCanonicalGuardedSmoothBaseMass
            R certificate deltaStar
              J.postHeightBridge.sampleData.W (K0 + 1) J.betaAct :=
        hqTildeActual
      _ =
          bankPaperCanonicalGuardedSmoothBaseMass
            R certificate deltaStar W (K0 + 1) betaAct := by
        rw [hBWpost, hbetaActSync]
      _ = qTilde Bsource.sampleData.n :=
        hqTildeFiber.symm
  have hupperTwo : ∀ sign, I.upper sign ≤ 2 :=
    fun sign => (hupperStrict sign).le
  have hupperBroadPost : ∀ sign,
      physicalBound (I.upper sign) J.postHeightBridge.sampleData.n ≤
        2 * J.postHeightBridge.sampleData.n -
          (K0 + 1) *
            upperTailLength c J.postHeightBridge.sampleData.n := by
    intro sign
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hupperBroadN sign
  have hroughDepthPost :
      (K0 + 1) *
          upperTailLength c J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.sampleData.n := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hroughDepthN
  have hqnOnePost : 1 ≤ J.qn := by
    rw [hfinalActiveMass]
    exact hqnOneN
  have hmassFamily :
      bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n ≤
        Cmass * secondOrderScale Bsource.sampleData.n := by
    have habs :
        |bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n| ≤
          Cmass * secondOrderScale Bsource.sampleData.n := by
      simpa only [Real.norm_eq_abs, abs_of_pos hscaleN] using
        hmassBoundN
    exact
      (le_abs_self
        (bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n)).trans habs
  have hmassUpper :
      J.qn ≤
        Cmass * (J.postHeightBridge.sampleData.n : Real) /
          J.postHeightBridge.L := by
    calc
      J.qn =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n :=
        hfinalActiveMass
      _ ≤ Cmass * secondOrderScale Bsource.sampleData.n :=
        hmassFamily
      _ =
          Cmass * (J.postHeightBridge.sampleData.n : Real) /
            J.postHeightBridge.L := by
        simp only [
          secondOrderScale, BridgeData.L,
          BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        ring
  have hcellDensity : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (J.postHeightBridge.sampleData.n : Real) ≤
        (Fintype.card
          (J.postHeightBridge.sampleData.SampleAt cell) : Real) := by
    intro cell
    have hcellFinset :
        J.postHeightBridge.sampleData.cellFinset cell =
          rawCell (PaperHeadSimplex.pattern P hprime E) I
              Bsource.sampleData.n cell \
            (roughCanonicalBridgeRelevantLedgerFamily
              depth Bsource.sampleData.n).guards := by
      calc
        J.postHeightBridge.sampleData.cellFinset cell =
            (canonicalSampleData
              (W := J.postHeightBridge.sampleData.W)
              (PaperHeadSimplex.pattern P hprime E) I
              (roughCanonicalBridgeRelevantLedgerFamily
                depth J.postHeightBridge.sampleData.n)
              hsep hremaining).cellFinset cell :=
          congrArg
            (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
              D.cellFinset cell)
            hcanonical
        _ =
            rawCell (PaperHeadSimplex.pattern P hprime E) I
                J.postHeightBridge.sampleData.n cell \
              (roughCanonicalBridgeRelevantLedgerFamily
                depth J.postHeightBridge.sampleData.n).guards :=
          canonicalSampleData_cellFinset
            (PaperHeadSimplex.pattern P hprime E) I
            (roughCanonicalBridgeRelevantLedgerFamily
              depth J.postHeightBridge.sampleData.n)
            hsep hremaining cell
        _ =
            rawCell (PaperHeadSimplex.pattern P hprime E) I
                Bsource.sampleData.n cell \
              (roughCanonicalBridgeRelevantLedgerFamily
                depth Bsource.sampleData.n).guards := by
          rfl
    have hcardEq :
        (Fintype.card
            (J.postHeightBridge.sampleData.SampleAt cell) : Real) =
          ((rawCell (PaperHeadSimplex.pattern P hprime E) I
              Bsource.sampleData.n cell \
            (roughCanonicalBridgeRelevantLedgerFamily
              depth Bsource.sampleData.n).guards).card : Real) := by
      rw [Fintype.card_coe, hcellFinset]
    have hdensityLe :
        density ≤
          paperCellDensity
              ((PaperHeadSimplex.pattern P hprime E) cell.1)
              (I.lower cell.2) (I.upper cell.2) / 4 := by
      simpa only [density] using
        bankPaperCanonicalGuardedCellDensityFloor_le
          (PaperHeadSimplex.pattern P hprime E) I cell
    calc
      density * (J.postHeightBridge.sampleData.n : Real) =
          density * (Bsource.sampleData.n : Real) := by
        rfl
      _ ≤
          (paperCellDensity
              ((PaperHeadSimplex.pattern P hprime E) cell.1)
              (I.lower cell.2) (I.upper cell.2) / 4) *
            (Bsource.sampleData.n : Real) :=
        mul_le_mul_of_nonneg_right hdensityLe (Nat.cast_nonneg _)
      _ =
          paperCellDensity
              ((PaperHeadSimplex.pattern P hprime E) cell.1)
              (I.lower cell.2) (I.upper cell.2) *
            (Bsource.sampleData.n : Real) / 4 := by
        ring
      _ ≤
          ((rawCell (PaperHeadSimplex.pattern P hprime E) I
              Bsource.sampleData.n cell \
            (roughCanonicalBridgeRelevantLedgerFamily
              depth Bsource.sampleData.n).guards).card : Real) :=
        hrawDensityN cell
      _ =
          (Fintype.card
            (J.postHeightBridge.sampleData.SampleAt cell) : Real) :=
        hcardEq.symm
  have hguardAgreementPost :
      BankPaperCanonicalBridgeGuardAgreement
        (roughCanonicalBridgeRelevantLedgerFamily
          depth J.postHeightBridge.sampleData.n)
        R certificate deltaStar := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hguardAgreementN R certificate
  have hmFrozenForSource :
      mFrozen Bsource.sampleData.n =
        bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K0 + 1)
          J.postHeightBridge R certificate deltaStar betaProt J.alpha := by
    simpa only [hbetaProtSync] using hmFrozen
  have hresidualForSource :
      BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
        (K := K0 + 1) J.postHeightBridge R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          J.Tsource deltaStar betaProt J.alpha J.beta
            (qTilde Bsource.sampleData.n) := by
    simpa only [hbetaProtSync, hqTildeFamily] using hsourceResidual
  have hsourceStateRaw :=
    hsourceN J.postHeightBridge rfl hBWpost
      hsep hremaining hcanonical R certificate hguardAgreementPost
      J.Tsource hsourceMargin
      (R.paperFixedExceptionalFactors deltaStar)
      J.alpha J.beta hmFrozenForSource hresidualForSource
  have hsourceState :
      BankPaperCanonicalSelectorSourceState
        (W := J.postHeightBridge.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.roundedSourceSelector := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedSourceSelector,
      hbetaProtSync, hqTildeFamily] using hsourceStateRaw
  exact
    exists_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_canonical
      (M := M) (hprime := hprime) (E := E) (hE := hE)
      (Bsource := Bsource) (R := R) (certificate := certificate)
      (I := I) (hlowerOne := hlowerOne) (hupperTwo := hupperTwo)
      (Cprom := 2) (Cbank := 0)
      (G := roughCanonicalBridgeRelevantLedgerFamily depth)
      (deltaStar := deltaStar) (mu := mu)
      (sourceMarginFloor := sourceMarginFloor)
      (headMarginFloor := headMarginFloor)
      (physicalEtaFloor := physicalEtaFloor)
      (postMarginFloor := postMarginFloor)
      (logY := logY) (Lambda0 := Lambda0)
      (mFrozen := mFrozen) (qTilde := qTilde)
      (hsourceMarginFloor := hsourceMarginFloor)
      (hheadMarginFloor := hheadMarginFloor)
      (hphysicalEtaFloor := hphysicalEtaFloor)
      (hpostMarginFloor := hpostMarginFloor)
      (hdelta := hdelta) (J := J)
      (hexponentSync := hexponentSync) (hhead := by
        simpa only [hBWpost] using hhead)
      (hsep := hsep) (hremaining := hremaining)
      (hcanonical := hcanonical)
      (hguardAgreement := hguardAgreementPost)
      (hupperBroad := hupperBroadPost)
      (hroughDepth := hroughDepthPost)
      (hqnOne := hqnOnePost)
      (hbetaProt := by
        simpa only [hbetaProtSync] using hbetaProt)
      (hsourceState := hsourceState)
      (Cmass := Cmass) (density := density)
      (hCmass := hCmass.le) (hdensity := hdensity)
      (hmassUpper := hmassUpper) (hcellDensity := hcellDensity)
      (hcombined := hcapacity.1) (hcharge := hcapacity.2)
      (hsourceMargin := hsourceMargin)
      (hheadMargin := hheadMargin)
      (hphysicalEta := hphysicalEta)
      (hpostMargin := hpostMargin)
      (hqTildeFamily := hqTildeFamily)
      (hmFrozen := hmFrozen)
      (hfinalActiveMass := by
        simpa only [qTilde] using hfinalActiveMass)
      (hsourceResidual := hsourceResidual)

end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal007_003 := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual
