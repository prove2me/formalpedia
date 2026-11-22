-- Prove2me | solution 1 for Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_centered_bound_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:10:41.85671+00:00
-- url     : https://prove2.me/submissions/091bd6a3-e43b-4980-b6e4-0584be50763c

import Definitions.Def_erdos390_remaining_analytic_propositions_004
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
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_uniformAverage_divInd_paper_bound

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























































end Erdos390.Full.ArithmeticModel

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







/-- A prefix strictly above `floor(A n)` has scale strictly above `A`. -/
theorem lt_prefixScale_of_physicalBound_lt
    {A : ℝ} {n k : ℕ} (hn : 0 < n)
    (hk : physicalBound A n < k) :
    A < prefixScale n k := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfloor : A * (n : ℝ) < (physicalBound A n : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (A * (n : ℝ))
  have hkCast : (physicalBound A n : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast hk
  apply (lt_div_iff₀ hnR).2
  exact hfloor.trans_le hkCast

/-- A prefix below `floor(C n)` has scale at most `C`. -/
theorem prefixScale_le_of_le_physicalBound
    {C : ℝ} {n k : ℕ} (hC : 0 ≤ C) (hn : 0 < n)
    (hk : k ≤ physicalBound C n) :
    prefixScale n k ≤ C := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkFloor : (k : ℝ) ≤ (physicalBound C n : ℝ) := by
    exact_mod_cast hk
  have hfloor : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg hC hnR.le)
  apply (div_le_iff₀ hnR).2
  exact hkFloor.trans hfloor

/-- Combined compact containment for every moving prefix used by Abel
summation. -/
theorem prefixScale_mem_compact
    {A C : ℝ} {n k : ℕ} (hC : 0 ≤ C) (hn : 0 < n)
    (hlow : physicalBound A n < k)
    (hhigh : k ≤ physicalBound C n) :
    A < prefixScale n k ∧ prefixScale n k ≤ C :=
  ⟨lt_prefixScale_of_physicalBound_lt hn hlow,
    prefixScale_le_of_le_physicalBound hC hn hhigh⟩















/-! ## Exact prefix normalization identities -/











theorem prefixFraction_nonneg_le_one
    {A C : ℝ} {n k : ℕ} (hAC : A < C)
    (hAD : A ≤ prefixScale n k) (hDC : prefixScale n k ≤ C) :
    0 ≤ prefixFraction A C n k ∧ prefixFraction A C n k ≤ 1 := by
  have hden : 0 < C - A := sub_pos.mpr hAC
  constructor
  · exact div_nonneg (sub_nonneg.mpr hAD) hden.le
  · apply (div_le_one hden).2
    linarith





/-- Uniform centered divisor/prefix covariance for the un-tilted structured
cell.  The main terms from the moving prefix, the full divisor profile, and
the prefix mass cancel exactly; the remaining loss retains `1/d`. -/
theorem exists_uniform_movingPrefix_divInd_centered_bound
    (P : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n k d : ℕ},
      N₀ ≤ n → physicalBound A n < k → k ≤ physicalBound C n →
      0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      let S := structuredCell P (physicalBound A n)
        (physicalBound C n) (yNat n)
      |DivisibilityMomentBounds.uniformAverage S
          (fun m ↦ divInd d m * if m ≤ k then 1 else 0) -
        DivisibilityMomentBounds.uniformAverage S (divInd d) *
          DivisibilityMomentBounds.uniformAverage S
            (fun m ↦ if m ≤ k then 1 else 0)| ≤
        K / ((d : ℝ) * Scale.L n) := by
  obtain ⟨Kjoint, hKjoint, Nj, hjoint⟩ :=
    exists_uniform_movingPrefix_uniformAverage_divInd_bound P hA hAC
  obtain ⟨Kdiv, hKdiv, Nd, hdiv⟩ :=
    exists_uniform_uniformAverage_divInd_paper_bound P hA hAC
  have hLTop : Filter.Tendsto Scale.L Filter.atTop Filter.atTop := by
    simpa [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLEvent : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ Scale.L n :=
    hLTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp hLEvent
  let Adiv : ℝ := Kdiv + 1 / DickmanBasic.rho DickmanBasic.U
  let K : ℝ := Kjoint + Kdiv + Adiv * Kjoint
  have hrho : 0 < DickmanBasic.rho DickmanBasic.U :=
    DickmanBasic.rho_U_pos
  have hAdiv : 0 < Adiv := by
    dsimp only [Adiv]
    exact add_pos_of_pos_of_nonneg hKdiv (one_div_nonneg.mpr hrho.le)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  let N₀ := max Nj (max Nd NL)
  refine ⟨K, hK, N₀, ?_⟩
  intro n k d hN hlow hhigh hd hd4 hdsmooth hcop
  dsimp only
  have hNj : Nj ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNd : Nd ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNl : NL ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hL1 : (1 : ℝ) ≤ Scale.L n := hNL n hNl
  have hn : 1 < n := by
    by_contra hnle
    have hLle : Scale.L n ≤ 0 := by
      unfold Scale.L
      rw [Real.log_nonpos_iff (by positivity)]
      exact_mod_cast Nat.le_of_not_gt hnle
    linarith
  have hL : 0 < Scale.L n := Scale.L_pos hn
  let S : Finset ℕ := structuredCell P (physicalBound A n)
    (physicalBound C n) (yNat n)
  let J : ℝ := DivisibilityMomentBounds.uniformAverage S
    (fun m ↦ divInd d m * if m ≤ k then 1 else 0)
  let a : ℝ := DivisibilityMomentBounds.uniformAverage S (divInd d)
  let b : ℝ := DivisibilityMomentBounds.uniformAverage S
    (fun m ↦ if m ≤ k then 1 else 0)
  let r : ℝ := prefixFraction A C n k
  let t : ℝ := paperDivisibilityMain n d
  have hjRaw := hjoint hNj hlow hhigh hd hd4 hdsmooth hcop
  have hJ : |J - r * t| ≤ Kjoint / ((d : ℝ) * Scale.L n) := by
    dsimp only [J, r, t, S]
    exact hjRaw.2
  have ha : |a - t| ≤ Kdiv / ((d : ℝ) * Scale.L n) := by
    dsimp only [a, t, S]
    exact (hdiv hNd hd hd4 hdsmooth hcop).2
  have hOneLe : 1 ≤ yNat n ^ 4 := (show 1 ≤ d by omega).trans hd4
  have hbRaw := hjoint (n := n) (k := k) (d := 1) hNj hlow hhigh
    (by omega) hOneLe (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hb : |b - r| ≤ Kjoint / Scale.L n := by
    dsimp only [b, r, S]
    simpa [paperDivisibilityMain_one, divInd] using hbRaw.2
  have hrange : 0 ≤ r ∧ r ≤ 1 := by
    dsimp only [r]
    have hcompact := prefixScale_mem_compact
      (hA.trans hAC).le (by omega : 0 < n) hlow hhigh
    exact prefixFraction_nonneg_le_one hAC hcompact.1.le hcompact.2
  have htRange := paperDivisibilityMain_nonneg_le hn hd hd4
  have ht0 : 0 ≤ t := by simpa only [t] using htRange.1
  have ha0 : 0 ≤ a := by
    dsimp only [a, DivisibilityMomentBounds.uniformAverage]
    exact div_nonneg (Finset.sum_nonneg fun m hm ↦ divInd_nonneg d m)
      (by positivity)
  have hdivL : Kdiv / ((d : ℝ) * Scale.L n) ≤ Kdiv / (d : ℝ) := by
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hden : (d : ℝ) ≤ (d : ℝ) * Scale.L n := by
      calc
        (d : ℝ) = (d : ℝ) * 1 := by ring
        _ ≤ (d : ℝ) * Scale.L n :=
          mul_le_mul_of_nonneg_left hL1 hdR.le
    exact div_le_div_of_nonneg_left hKdiv.le hdR hden
  have haUpper : a ≤ Adiv / (d : ℝ) := by
    have hdiff : a - t ≤ |a - t| := le_abs_self (a - t)
    have htUpper : t ≤
        1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ)) := by
      simpa only [t] using htRange.2
    calc
      a = (a - t) + t := by ring
      _ ≤ |a - t| + t := by linarith
      _ ≤ Kdiv / ((d : ℝ) * Scale.L n) +
          1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ)) :=
        add_le_add ha htUpper
      _ ≤ Kdiv / (d : ℝ) +
          1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ)) :=
        add_le_add hdivL (le_refl _)
      _ = Adiv / (d : ℝ) := by
        dsimp only [Adiv]
        field_simp [hrho.ne', (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]
  have hidentity : J - a * b =
      (J - r * t) + r * (t - a) + a * (r - b) := by ring
  rw [hidentity]
  have htri :
      |(J - r * t) + r * (t - a) + a * (r - b)| ≤
        |J - r * t| + r * |t - a| + a * |r - b| := by
    calc
      _ ≤ |(J - r * t) + r * (t - a)| + |a * (r - b)| :=
        abs_add_le _ _
      _ ≤ (|J - r * t| + |r * (t - a)|) + |a * (r - b)| :=
        add_le_add (abs_add_le _ _) (le_refl _)
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hrange.1,
        abs_of_nonneg ha0]
  refine htri.trans ?_
  have hta : |t - a| ≤ Kdiv / ((d : ℝ) * Scale.L n) := by
    simpa only [abs_sub_comm t] using ha
  have hrb : |r - b| ≤ Kjoint / Scale.L n := by
    simpa only [abs_sub_comm r] using hb
  have hscaleDiv : 0 ≤ Kdiv / ((d : ℝ) * Scale.L n) := by positivity
  have hscaleJoint : 0 ≤ Kjoint / Scale.L n := by positivity
  calc
    |J - r * t| + r * |t - a| + a * |r - b| ≤
        Kjoint / ((d : ℝ) * Scale.L n) +
          r * (Kdiv / ((d : ℝ) * Scale.L n)) +
          a * (Kjoint / Scale.L n) := by
      exact add_le_add
        (add_le_add hJ (mul_le_mul_of_nonneg_left hta hrange.1))
        (mul_le_mul_of_nonneg_left hrb ha0)
    _ ≤ Kjoint / ((d : ℝ) * Scale.L n) +
          Kdiv / ((d : ℝ) * Scale.L n) +
          (Adiv / (d : ℝ)) * (Kjoint / Scale.L n) := by
      exact add_le_add
        (add_le_add (le_refl _)
          (mul_le_of_le_one_left hscaleDiv hrange.2))
        (mul_le_mul_of_nonneg_right haUpper hscaleJoint)
    _ = K / ((d : ℝ) * Scale.L n) := by
      dsimp only [K]
      field_simp [hL.ne', (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]



end

end Erdos390.Full.PaperMovingPrefixMarkedCell

end

theorem solution : Erdos390.RemainingAnalyticGoal004_005 := by
  exact @Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_centered_bound
