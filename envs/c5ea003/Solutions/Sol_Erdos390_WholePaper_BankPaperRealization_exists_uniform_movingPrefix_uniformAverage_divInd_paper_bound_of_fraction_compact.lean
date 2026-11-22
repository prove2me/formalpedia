-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_uniformAverage_divInd_paper_bound_of_fraction_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:10:04.187383+00:00
-- url     : https://prove2.me/submissions/fe2c145e-3a17-4104-9d10-47ca087e2b9f

import Definitions.Def_erdos390_remaining_analytic_propositions_007
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_PaperMovingPrefixMarkedCell_exists_uniform_movingPrefix_uniformAverage_divInd_bound

/- Source module: Erdos390.Full.DivisibilityMomentBounds -/
section


/-!
# Exact multiple-counting moment bounds

The omitted-local-score step in Lemma 7.5 expands a valuation score into
divisor indicators and then counts common multiples.  This file proves that
finite combinatorial step for an arbitrary set of positive integers bounded
by one physical endpoint.  No smooth-number estimate or probability-model
assumption enters here.
-/

open scoped BigOperators

namespace Erdos390.Full.DivisibilityMomentBounds

open ArithmeticModel

noncomputable section



/-- A finite sum of an actual divisor indicator is the cardinality of the
corresponding filtered set. -/
theorem sum_divInd_eq_card_filter (S : Finset ℕ) (D : ℕ) :
    (∑ m ∈ S, divInd D m) = ((S.filter (D ∣ ·)).card : ℝ) := by
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [divInd]































end

end Erdos390.Full.DivisibilityMomentBounds

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















/-! ## The common paper-scale main term -/

















/-- Four marks keep the paper coordinate inside the range on which the
constructed Dickman function is positive. -/
theorem paperDivisorCoordinate_mem_zero_five {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisorCoordinate n d ∧ paperDivisorCoordinate n d ≤ 5 := by
  have hnpos : 0 < n := by omega
  have hypos : 0 < y n := y_pos hnpos
  have hylog : 0 < Real.log (y n) := by
    rw [log_y hnpos]
    exact mul_pos (by norm_num) (L_pos hn)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  have hyNatPos : 0 < yNat n := by
    by_contra hnot
    have hyNat0 : yNat n = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hyNat0] at hd4
    omega
  have hyNatRpos : (0 : ℝ) < (yNat n : ℝ) := by exact_mod_cast hyNatPos
  have hdCast : (d : ℝ) ≤ (yNat n : ℝ) ^ 4 := by exact_mod_cast hd4
  have hlogdNat : Real.log (d : ℝ) ≤
      4 * Real.log (yNat n : ℝ) := by
    have h := Real.log_le_log hdR hdCast
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hyNatUpper : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le hypos.le
  have hlogNatY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatRpos hyNatUpper
  have hlogdY : Real.log (d : ℝ) ≤ 4 * Real.log (y n) := by
    calc
      Real.log (d : ℝ) ≤ 4 * Real.log (yNat n : ℝ) := hlogdNat
      _ ≤ 4 * Real.log (y n) := by linarith
  have hquot0 : 0 ≤ Real.log (d : ℝ) / Real.log (y n) :=
    div_nonneg hlogd0 hylog.le
  have hquot4 : Real.log (d : ℝ) / Real.log (y n) ≤ 4 :=
    (div_le_iff₀ hylog).2 (by simpa using hlogdY)
  unfold paperDivisorCoordinate DickmanBasic.U
  constructor <;> linarith

theorem paperDivisibilityMain_nonneg_le {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisibilityMain n d ∧
      paperDivisibilityMain n d ≤
        1 / (rho DickmanBasic.U * (d : ℝ)) := by
  have hv := paperDivisorCoordinate_mem_zero_five hn hd hd4
  have hrv : 0 < rho (paperDivisorCoordinate n d) :=
    rho_pos_on_zero_five hv.1 hv.2
  have hrv1 : rho (paperDivisorCoordinate n d) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hv.2
  have hrU : 0 < rho DickmanBasic.U := rho_U_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold paperDivisibilityMain
  constructor
  · positivity
  · rw [div_div]
    exact div_le_div_of_nonneg_right hrv1 (mul_pos hrU hdR).le



















/-! ## Normalization algebra -/











end

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.Full.PaperMovingPrefixMarkedCell -/
section


/-!
# Uniform moving-prefix endpoint bookkeeping

For a prefix endpoint `k` inside a fixed physical interval, put
`D = k / n`.  Then `physicalBound D n = k` exactly.  Moreover `D` stays
in the original fixed compact physical interval.  These elementary facts
allow the marked-cell endpoint theorem to be applied without pretending
that the moving endpoint is fixed as `n` varies.
-/

namespace Erdos390.Full.PaperMovingPrefixMarkedCell

open ArithmeticModel PaperScaleMarkedCell
open HeadPattern StructuredCells MarkedFriableAsymptotic
open StructuredCellAsymptotic
open scoped BigOperators

noncomputable section



























/-! ## Exact prefix normalization identities -/

theorem structuredCell_filter_le_eq
    (P : Pattern) {lo hi y k : ℕ} (hk : k ≤ hi) :
    (structuredCell P lo hi y).filter (fun m ↦ m ≤ k) =
      structuredCell P lo k y := by
  ext m
  simp only [Finset.mem_filter, mem_structuredCell, mem_smoothInterval]
  constructor
  · rintro ⟨⟨⟨hlom, hmhi, hsmooth⟩, hmatch⟩, hmk⟩
    exact ⟨⟨hlom, hmk, hsmooth⟩, hmatch⟩
  · rintro ⟨⟨hlom, hmk, hsmooth⟩, hmatch⟩
    exact ⟨⟨⟨hlom, hmk.trans hk, hsmooth⟩, hmatch⟩, hmk⟩

/-- The joint divisor/prefix counting average is literally the normalized
moving marked-cell cardinality. -/
theorem uniformAverage_divInd_mul_prefix_eq_markedCell_ratio
    (P : Pattern) {lo hi y k d : ℕ} (hk : k ≤ hi) :
    DivisibilityMomentBounds.uniformAverage
        (structuredCell P lo hi y)
        (fun m ↦ divInd d m * if m ≤ k then 1 else 0) =
      ((markedCell P lo k y d).card : ℝ) /
        ((structuredCell P lo hi y).card : ℝ) := by
  unfold DivisibilityMomentBounds.uniformAverage
  have hsum :
      (∑ m ∈ structuredCell P lo hi y,
          (divInd d m * if m ≤ k then 1 else 0)) =
        ∑ m ∈ (structuredCell P lo hi y).filter (fun m ↦ m ≤ k),
          divInd d m := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmk : m ≤ k <;> simp [hmk]
  rw [hsum, structuredCell_filter_le_eq P hk,
    DivisibilityMomentBounds.sum_divInd_eq_card_filter]
  rfl



/-- Quantitative normalization with an arbitrary nonnegative target. -/
theorem abs_normalized_ratio_sub_le
    {x y q z E F : ℝ} (hq : 0 < q) (hyhalf : q / 2 ≤ y)
    (hx : |x - q * z| ≤ E) (hy : |y - q| ≤ F) (hz : 0 ≤ z) :
    |x / y - z| ≤ 2 * (E + z * F) / q := by
  have hypos : 0 < y := (half_pos hq).trans_le hyhalf
  have hE : 0 ≤ E := (abs_nonneg (x - q * z)).trans hx
  have hF : 0 ≤ F := (abs_nonneg (y - q)).trans hy
  have hnum : 0 ≤ E + z * F := add_nonneg hE (mul_nonneg hz hF)
  have hinv : 1 / y ≤ 2 / q := by
    apply (div_le_div_iff₀ hypos hq).2
    linarith
  have hid : x / y - z = (x - q * z + z * (q - y)) / y := by
    field_simp [hypos.ne']
    ring
  rw [hid, abs_div, abs_of_pos hypos]
  calc
    |x - q * z + z * (q - y)| / y ≤
        (|x - q * z| + |z * (q - y)|) / y := by
      exact div_le_div_of_nonneg_right (abs_add_le _ _) hypos.le
    _ = (|x - q * z| + z * |y - q|) / y := by
      rw [abs_mul, abs_of_nonneg hz, abs_sub_comm q y]
    _ ≤ (E + z * F) / y := by
      apply div_le_div_of_nonneg_right _ hypos.le
      exact add_le_add hx (mul_le_mul_of_nonneg_left hy hz)
    _ = (E + z * F) * (1 / y) := by ring
    _ ≤ (E + z * F) * (2 / q) :=
      mul_le_mul_of_nonneg_left hinv hnum
    _ = 2 * (E + z * F) / q := by ring













end

end Erdos390.Full.PaperMovingPrefixMarkedCell

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureMoving -/
section


/-!
# Sharp moving-prefix valuation profile for the smooth source

The label-one broad pool has a moving upper endpoint, so it is not one of the
fixed physical cells handled by the preceding file.  This file normalizes the
existing joint divisor/prefix theorem by the prefix mass, proves a uniform
reciprocal fallback on prefixes of fixed positive relative length, and then
sums the literal prime-power decomposition.

No comparison with a guarded pool, and no `O(1 / (p L))` conclusion, is used
as an input.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PrimePowerCovariance
open Erdos390.Full.PrimePowerCutoffCovariance
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.PaperMovingPrefixMarkedCell
open Erdos390.Full.PaperPrimePowerTailRate
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.LocalFugacityBounds
open Erdos390.Full.ValuationScoreDomination

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Exact conditional-prefix normalization -/

/-- The mass of a physical prefix under the full-cell counting law is exactly
the ratio of the two literal cardinalities. -/
theorem uniformAverage_movingPrefix_indicator_eq_card_ratio
    (P : Pattern) {lo hi y k : Nat} (hk : k ≤ hi) :
    DivisibilityMomentBounds.uniformAverage
        (structuredCell P lo hi y)
        (fun m ↦ if m ≤ k then 1 else 0) =
      ((structuredCell P lo k y).card : Real) /
        ((structuredCell P lo hi y).card : Real) := by
  have hraw :=
    uniformAverage_divInd_mul_prefix_eq_markedCell_ratio
      P (lo := lo) (hi := hi) (y := y) (k := k) (d := 1) hk
  simpa [divInd, markedCell] using hraw

/-- Dividing the joint divisor/prefix probability by the prefix mass gives
the literal uniform divisor average on the moving prefix. -/
theorem uniformAverage_movingPrefix_divInd_eq_joint_div_prefixMass
    (P : Pattern) {lo hi y k d : Nat} (hk : k ≤ hi)
    (hfull : (structuredCell P lo hi y).Nonempty)
    (hprefix : (structuredCell P lo k y).Nonempty) :
    DivisibilityMomentBounds.uniformAverage
        (structuredCell P lo k y) (divInd d) =
      DivisibilityMomentBounds.uniformAverage
          (structuredCell P lo hi y)
          (fun m ↦ divInd d m * if m ≤ k then 1 else 0) /
        DivisibilityMomentBounds.uniformAverage
          (structuredCell P lo hi y)
          (fun m ↦ if m ≤ k then 1 else 0) := by
  rw [uniformAverage_divInd_mul_prefix_eq_markedCell_ratio P hk]
  rw [uniformAverage_movingPrefix_indicator_eq_card_ratio P hk]
  unfold DivisibilityMomentBounds.uniformAverage
  rw [DivisibilityMomentBounds.sum_divInd_eq_card_filter]
  have hfullCard :
      ((structuredCell P lo hi y).card : Real) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hfull
  have hprefixCard :
      ((structuredCell P lo k y).card : Real) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hprefix
  change
    ((markedCell P lo k y d).card : Real) /
          ((structuredCell P lo k y).card : Real) =
      (((markedCell P lo k y d).card : Real) /
          ((structuredCell P lo hi y).card : Real)) /
        (((structuredCell P lo k y).card : Real) /
          ((structuredCell P lo hi y).card : Real))
  field_simp [hfullCard, hprefixCard]

/-! ## Sharp divisor profiles on positive-length prefixes -/

/-- Every moving prefix occupying a fixed positive proportion of its ambient
physical cell has the same normalized Dickman divisor profile, with the
sharp `1 / (d * L)` error. -/
theorem
    exists_uniform_movingPrefix_uniformAverage_divInd_paper_bound_of_fraction
    (P : Pattern) {A C rmin : Real}
    (hA : 0 < A) (hAC : A < C) (hrmin : 0 < rmin) :
    ∃ K : Real, 0 < K ∧ ∃ N₀ : Nat,
      ∀ {n k d : Nat}, N₀ ≤ n →
        physicalBound A n < k → k ≤ physicalBound C n →
        rmin ≤ prefixFraction A C n k →
        0 < d → d ≤ yNat n ^ 4 →
        d ∈ Nat.smoothNumbers (yNat n + 1) →
        Nat.Coprime d P.modulus →
        let S := structuredCell P (physicalBound A n) k (yNat n)
        ∃ _hS : S.Nonempty,
          |DivisibilityMomentBounds.uniformAverage S (divInd d) -
              paperDivisibilityMain n d| ≤
            K / ((d : Real) * L n) := by
  obtain ⟨Kjoint, hKjoint, Njoint, hjoint⟩ :=
    exists_uniform_movingPrefix_uniformAverage_divInd_bound P hA hAC
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlargeL : ∀ᶠ n : Nat in atTop,
      2 * Kjoint / rmin ≤ L n :=
    hLTop.eventually (eventually_ge_atTop (2 * Kjoint / rmin))
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp hlargeL
  have hrho : 0 < DickmanBasic.rho DickmanBasic.U :=
    DickmanBasic.rho_U_pos
  let Aprofile : Real := Kjoint + Kjoint / DickmanBasic.rho DickmanBasic.U
  let K : Real := 2 * Aprofile / rmin
  have hAprofile : 0 < Aprofile := by
    dsimp only [Aprofile]
    exact add_pos_of_pos_of_nonneg hKjoint
      (div_nonneg hKjoint.le hrho.le)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, max Njoint NL, ?_⟩
  intro n k d hN hlow hhigh hfrac hd hd4 hdsmooth hcop
  dsimp only
  have hNjoint : Njoint ≤ n := by omega
  have hNLbound : NL ≤ n := by omega
  have hLlarge := hNL n hNLbound
  have hn : 1 < n := by
    by_contra hnle
    have hLle : L n ≤ 0 := by
      unfold L
      rw [Real.log_nonpos_iff (by positivity)]
      exact_mod_cast Nat.le_of_not_gt hnle
    have hlargePos : 0 < 2 * Kjoint / rmin := by positivity
    linarith
  have hL : 0 < L n := L_pos hn
  have hdR : (0 : Real) < d := by exact_mod_cast hd
  let Sfull := structuredCell P
    (physicalBound A n) (physicalBound C n) (yNat n)
  let S := structuredCell P (physicalBound A n) k (yNat n)
  let x : Real := DivisibilityMomentBounds.uniformAverage Sfull
    (fun m ↦ divInd d m * if m ≤ k then 1 else 0)
  let b : Real := DivisibilityMomentBounds.uniformAverage Sfull
    (fun m ↦ if m ≤ k then 1 else 0)
  let r : Real := prefixFraction A C n k
  let t : Real := paperDivisibilityMain n d
  have hjRaw :=
    hjoint hNjoint hlow hhigh hd hd4 hdsmooth hcop
  have hfull : Sfull.Nonempty := by
    simpa only [Sfull] using hjRaw.1
  have hx :
      |x - r * t| ≤ Kjoint / ((d : Real) * L n) := by
    simpa only [x, r, t, Sfull] using hjRaw.2
  have hOneLe : 1 ≤ yNat n ^ 4 :=
    (show 1 ≤ d by omega).trans hd4
  have hbRaw :=
    hjoint (n := n) (k := k) (d := 1) hNjoint hlow hhigh
      (by omega) hOneLe (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hb :
      |b - r| ≤ Kjoint / L n := by
    dsimp only [b, r, Sfull]
    simpa [paperDivisibilityMain_one, divInd] using hbRaw.2
  have hrpos : 0 < r := by
    dsimp only [r]
    exact hrmin.trans_le hfrac
  have hKoverL : Kjoint / L n ≤ rmin / 2 := by
    have htwoK : 2 * Kjoint ≤ L n * rmin :=
      (div_le_iff₀ hrmin).mp hLlarge
    apply (div_le_iff₀ hL).2
    nlinarith
  have hbLower : r / 2 ≤ b := by
    have hdiff : r - b ≤ |b - r| := by
      rw [abs_sub_comm]
      exact le_abs_self (r - b)
    have hminHalf : rmin / 2 ≤ r / 2 := by linarith
    linarith
  have hbpos : 0 < b := (half_pos hrpos).trans_le hbLower
  have hmassExact :
      b = ((S.card : Real) / (Sfull.card : Real)) := by
    dsimp only [b, S, Sfull]
    exact uniformAverage_movingPrefix_indicator_eq_card_ratio P hhigh
  have hSCardPos : 0 < (S.card : Real) := by
    rw [hmassExact] at hbpos
    rcases (div_pos_iff.mp hbpos) with hcase | hcase
    · exact hcase.1
    · have hnot : ¬(Sfull.card : Real) < 0 :=
        not_lt_of_ge (by positivity)
      exact (hnot hcase.2).elim
  have hS : S.Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hSCardPos)
  refine ⟨hS, ?_⟩
  have htRange := paperDivisibilityMain_nonneg_le hn hd hd4
  have ht0 : 0 ≤ t := by simpa only [t] using htRange.1
  have htUpper :
      t ≤ 1 / (DickmanBasic.rho DickmanBasic.U * (d : Real)) := by
    simpa only [t] using htRange.2
  have hratio :=
    abs_normalized_ratio_sub_le hrpos hbLower hx hb ht0
  have hF0 : 0 ≤ Kjoint / L n :=
    div_nonneg hKjoint.le hL.le
  have htF :
      t * (Kjoint / L n) ≤
        (1 / (DickmanBasic.rho DickmanBasic.U * (d : Real))) *
          (Kjoint / L n) :=
    mul_le_mul_of_nonneg_right htUpper hF0
  have hnumerator :
      Kjoint / ((d : Real) * L n) +
          t * (Kjoint / L n) ≤
        Aprofile / ((d : Real) * L n) := by
    calc
      Kjoint / ((d : Real) * L n) +
          t * (Kjoint / L n) ≤
        Kjoint / ((d : Real) * L n) +
          (1 / (DickmanBasic.rho DickmanBasic.U * (d : Real))) *
            (Kjoint / L n) :=
          add_le_add (le_refl _) htF
      _ = Aprofile / ((d : Real) * L n) := by
        dsimp only [Aprofile]
        field_simp [hrho.ne', hdR.ne', hL.ne']
  have hnum0 :
      0 ≤ Aprofile / ((d : Real) * L n) := by positivity
  have hbound :
      2 *
          (Kjoint / ((d : Real) * L n) +
            t * (Kjoint / L n)) / r ≤
        K / ((d : Real) * L n) := by
    calc
      2 *
          (Kjoint / ((d : Real) * L n) +
            t * (Kjoint / L n)) / r ≤
        2 * (Aprofile / ((d : Real) * L n)) / r := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnumerator (by norm_num)) hrpos.le
      _ ≤ 2 * (Aprofile / ((d : Real) * L n)) / rmin := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) hnum0) hrmin hfrac
      _ = K / ((d : Real) * L n) := by
        dsimp only [K]
        field_simp [hrmin.ne', hdR.ne', hL.ne']
  rw [
    uniformAverage_movingPrefix_divInd_eq_joint_div_prefixMass
      P hhigh hfull hS]
  change |x / b - t| ≤ _
  exact hratio.trans hbound

/-! ## Reciprocal fallback on positive-length prefixes -/





/-! ## Full valuation on the moving prefix -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal007_008 := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_uniformAverage_divInd_paper_bound_of_fraction
