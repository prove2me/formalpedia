-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_density_lower_bound_of_fraction_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:09:38.176514+00:00
-- url     : https://prove2.me/submissions/992f4e41-993f-4b6d-8c66-6239481c5d1b

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
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound

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



/-! ## Sharp divisor profiles on positive-length prefixes -/



/-! ## Reciprocal fallback on positive-length prefixes -/

/-- Positive relative prefix length supplies a uniform linear density lower
bound, expressed at the physical upper scale used by the elementary multiple
counting fallback. -/
theorem exists_uniform_movingPrefix_density_lower_bound_of_fraction
    (P : Pattern) {A C rmin : Real}
    (hA : 0 < A) (hAC : A < C) (hC : 0 < C) (hrmin : 0 < rmin) :
    ∃ cprefix : Real, 0 < cprefix ∧ ∃ N₀ : Nat,
      ∀ {n k : Nat}, N₀ ≤ n →
        physicalBound A n < k → k ≤ physicalBound C n →
        rmin ≤ prefixFraction A C n k →
        0 < physicalBound C n ∧
          cprefix * (physicalBound C n : Real) ≤
            ((structuredCell P (physicalBound A n) k (yNat n)).card :
              Real) := by
  obtain ⟨Kjoint, hKjoint, Njoint, hjoint⟩ :=
    exists_uniform_movingPrefix_uniformAverage_divInd_bound P hA hAC
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound P hA hAC
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlargeL : ∀ᶠ n : Nat in atTop,
      2 * Kjoint / rmin ≤ L n :=
    hLTop.eventually (eventually_ge_atTop (2 * Kjoint / rmin))
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp hlargeL
  have hphysEvent : ∀ᶠ n : Nat in atTop,
      1 ≤ physicalBound C n := by
    have hcastTop : Tendsto (fun n : Nat ↦ (n : Real)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    filter_upwards [hcastTop.eventually
      (eventually_ge_atTop (1 / C))] with n hn
    unfold physicalBound
    apply Nat.le_floor
    have := (div_le_iff₀ hC).mp hn
    exact_mod_cast (show (1 : Real) ≤ C * (n : Real) by
      simpa [mul_comm] using this)
  obtain ⟨Nphys, hNphys⟩ := Filter.eventually_atTop.mp hphysEvent
  let cfull : Real := paperCellDensity P A C
  have hcfull : 0 < cfull := paperCellDensity_pos P hAC
  let cprefix : Real := rmin * cfull / (4 * C)
  have hcprefix : 0 < cprefix := by
    dsimp only [cprefix]
    positivity
  refine ⟨cprefix, hcprefix,
    max 2 (max Njoint (max Ndensity (max NL Nphys))), ?_⟩
  intro n k hN hlow hhigh hfrac
  have hn : 1 < n := by omega
  have hNjoint : Njoint ≤ n := by omega
  have hNdensity : Ndensity ≤ n := by omega
  have hNLbound : NL ≤ n := by omega
  have hNphysBound : Nphys ≤ n := by omega
  have hL : 0 < L n := L_pos hn
  have hLlarge := hNL n hNLbound
  have hMpos : 0 < physicalBound C n := by
    have := hNphys n hNphysBound
    omega
  let Sfull := structuredCell P
    (physicalBound A n) (physicalBound C n) (yNat n)
  let S := structuredCell P (physicalBound A n) k (yNat n)
  let b : Real := DivisibilityMomentBounds.uniformAverage Sfull
    (fun m ↦ if m ≤ k then 1 else 0)
  let r : Real := prefixFraction A C n k
  have hOneLe : 1 ≤ yNat n ^ 4 := by
    have hYone : 1 ≤ yNat n := by
      rw [yNat]
      apply Nat.le_floor
      rw [y]
      have hnOneR : (1 : Real) ≤ (n : Real) := by
        exact_mod_cast (show 1 ≤ n by omega)
      simpa only [Nat.cast_one] using
        Real.one_le_rpow hnOneR
          (by norm_num : (0 : Real) ≤ 2 / 9)
    exact one_le_pow₀ hYone
  have hbRaw :=
    hjoint (n := n) (k := k) (d := 1) hNjoint hlow hhigh
      (by omega) hOneLe (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hfull : Sfull.Nonempty := by
    simpa only [Sfull] using hbRaw.1
  have hb :
      |b - r| ≤ Kjoint / L n := by
    dsimp only [b, r, Sfull]
    simpa [paperDivisibilityMain_one, divInd] using hbRaw.2
  have hKoverL : Kjoint / L n ≤ rmin / 2 := by
    have htwoK : 2 * Kjoint ≤ L n * rmin :=
      (div_le_iff₀ hrmin).mp hLlarge
    apply (div_le_iff₀ hL).2
    nlinarith
  have hbLower : rmin / 2 ≤ b := by
    have hdiff : r - b ≤ |b - r| := by
      rw [abs_sub_comm]
      exact le_abs_self (r - b)
    have hrLower : rmin ≤ r := by simpa only [r] using hfrac
    linarith
  have hmassExact :
      b = ((S.card : Real) / (Sfull.card : Real)) := by
    dsimp only [b, S, Sfull]
    exact uniformAverage_movingPrefix_indicator_eq_card_ratio P hhigh
  have hfullCard :
      (0 : Real) < (Sfull.card : Real) := by
    exact_mod_cast Finset.card_pos.mpr hfull
  have hcardEq :
      (S.card : Real) = b * (Sfull.card : Real) := by
    rw [hmassExact]
    field_simp [hfullCard.ne']
  have hfullDensity :
      cfull * (n : Real) / 2 ≤ (Sfull.card : Real) := by
    simpa only [cfull, Sfull] using hdensity hNdensity
  have hprod :
      (rmin / 2) * (cfull * (n : Real) / 2) ≤
        b * (Sfull.card : Real) := by
    exact mul_le_mul hbLower hfullDensity
      (by positivity) (by linarith)
  have hMcast :
      (physicalBound C n : Real) ≤ C * (n : Real) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  refine ⟨hMpos, ?_⟩
  calc
    cprefix * (physicalBound C n : Real) ≤
        cprefix * (C * (n : Real)) :=
      mul_le_mul_of_nonneg_left hMcast hcprefix.le
    _ = (rmin / 2) * (cfull * (n : Real) / 2) := by
      dsimp only [cprefix]
      field_simp [hC.ne']
      ring
    _ ≤ b * (Sfull.card : Real) := hprod
    _ = (S.card : Real) := hcardEq.symm



/-! ## Full valuation on the moving prefix -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal007_007 := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_density_lower_bound_of_fraction
