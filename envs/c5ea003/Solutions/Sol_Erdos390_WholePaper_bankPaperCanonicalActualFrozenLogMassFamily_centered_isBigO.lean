-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:01:26.801688+00:00
-- url     : https://prove2.me/submissions/dd7a4759-7389-4078-8fc5-3f2361d31202

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_008

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

/-- Hence the chosen tail length is eventually at most `n`. -/
theorem eventually_upperTailLength_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, upperTailLength c n ≤ n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratio hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcast : (upperTailLength c n : ℝ) ≤ (n : ℝ) := by
    have hratioLe :
        (upperTailLength c n : ℝ) / (n : ℝ) ≤ 1 := hratio.le
    have := (div_le_iff₀ hnReal).mp hratioLe
    simpa only [one_mul] using this
  exact_mod_cast hcast



/-- A tail of length at most `n` gives an endpoint at most `3n`. -/
theorem upperEndpoint_le_three_mul {n h : ℕ} (hh : h ≤ n) :
    upperEndpoint n h ≤ 3 * n := by
  simp only [upperEndpoint]
  omega















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













/-- Every active sample coordinate lies in the literal guarded candidate
set selected for the prebridge. -/
theorem bankPaperCanonicalActiveSeed_value_mem_candidates
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (m : D.Sample) : D.value m ∈ candidates := by
  exact H.2.2.1 m



/-- The ambient seed is dominated by the guarded pre-selector on every
candidate coordinate. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_le_preSelector
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    {a : Nat} (ha : a ∈ candidates) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a <=
      preSelector a := by
  exact H.2.2.2 a ha







/-! ## The actual scaled bridge data -/









/-! ## Tagged frozen remainder and exact push-forward -/











/-- Summing the ambient push-forward over all guarded candidates recovers
the tagged active mass exactly, even before using value-map injectivity. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    (∑ a ∈ candidates,
      bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a) =
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
    bankPaperCanonicalLiteralActiveMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (bankPaperCanonicalActiveSeed_value_mem_candidates H m)).elim





/-- The total frozen remainder is the pre-selector mass minus the literal
active mass. -/
theorem sum_bankPaperCanonicalActualFrozenWeight
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
        D candidates preSelector activeSeed a) =
      (∑ a ∈ candidates, preSelector a) -
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActualFrozenWeight
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
    (fun a => preSelector a)]
  rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
    (fun a => bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a)]
  rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass H]



/-! ## The initial combined selector -/









/-! ## The literal active marked target and endpoint -/













/-! ## Smooth active support and unchanged complete-rough rows -/























/-! ## Prime support, exact bands, and the derived prefix ledger -/











/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic -/
section


/-!
# Asymptotic package for the fixed exceptional low-prime charge

This file records the constants and scale arithmetic used after the finite
weighted Selberg decomposition of `G_fix` has been proved.  In the notation
of the paper,

* `paperExceptionalSelbergMainConstant` is `C_S`;
* `paperExceptionalSelbergRemainderConstant` is `C_R`;
* `paperExceptionalChargeConstant c` is `A_exc(c)`;
* `paperExceptionalChargeEpsilon deltaStar n` is the normalized
  endpoint/remainder coefficient.

The finite majorant below is obtained by composing the separate finite
rough/smooth-fibre argument with the elementary valuation-prefix estimates.
Nothing in this file assumes that the actual exceptional charge satisfies
that majorant.  We prove the finite charge bound and its analytic packaging,
together with the independent arithmetic support fact that, under the
displayed paper-range hypotheses, the actual low-prime charge is exactly
zero above twice the paper's literal real exceptional cutoff.  The
corresponding safe integral-cutoff statement is retained as a corollary.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Auditable paper constants -/

















/-! ## The finite Selberg output and its normalized remainder -/











/-! ## The endpoint remainder tends to zero -/





/-! ## Uniform packaging of the finite majorant -/

/-- Eventually the literal tail ceiling is at most `2cN`. -/
theorem eventually_upperTailLength_cast_le_two_mul_secondOrderScale
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) ≤
        2 * c * secondOrderScale n := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / secondOrderScale n ≤
        2 * c :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_le_nhds (by linarith : c < 2 * c))
  filter_upwards [hratio, eventually_secondOrderScale_pos] with n hn hscale
  exact (div_le_iff₀ hscale).mp hn







/-! ## Exact support cutoff for the actual fixed charge -/







/-! ## Closing the finite weighted Selberg estimate -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector -/
section


/-!
# Actual-data connector for the Section 8 analytic ledger

The reduced Section 8 ledger still names the actual post-guard active mass
and the exact frozen mass/logarithmic ledgers.  The Proposition 8.7 actual-
data connector already supplies the finite decomposition needed to make
those objects literal: every guarded candidate is split into its active
seed and its frozen remainder.

This file adjoins the frozen integral factors, defines the resulting exact
total frozen mass and logarithmic contribution, and proves

`m0 + qTilde = #fixed + sum candidates preSelector`

whenever the actual active-measure constructor holds.  Consequently the
first frozen-baseline estimate reduces to the rough selector's literal
total-mass estimate.  For the canonical scaled seed, its active mass is
exactly the guarded smooth base.  Exact interval support then centers the
frozen logarithmic contribution, while the complete central-tail product
satisfies `logY = h * L + O(secondOrderScale)` by elementary factor bounds.
The generic interval-geometry theorem exposes the selector total-mass
estimate, and the final constructed-quota theorem proves that estimate from
the rough-stage frozen baseline ledger, nearest-integer construction, and
the existing `d = O(secondOrderScale / L)` theorem.

No abstract `qTilde`, `m0`, or `Lambda0` remains in the final theorem.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

/-! ## Literal frozen mass and logarithmic contribution -/





/-- The actual-data split identifies the total frozen mass with the fixed
integral count plus candidate selector mass minus literal active mass. -/
theorem bankPaperCanonicalActualFrozenTotalMass_eq
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    bankPaperCanonicalActualFrozenTotalMass
        D fixed bankBase candidates preSelector activeSeed =
      (fixed.card : Real) + (bankBase.card : Real) +
        (∑ a ∈ candidates, preSelector a) -
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  unfold bankPaperCanonicalActualFrozenTotalMass
  rw [sum_bankPaperCanonicalActualFrozenWeight H]
  ring

/-- Equivalently, adjoining the literal active mass recovers the complete
fixed-plus-selector mass with no error term. -/
theorem bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    bankPaperCanonicalActualFrozenTotalMass
          D fixed bankBase candidates preSelector activeSeed +
        bankPaperCanonicalLiteralActiveMass D activeSeed =
      (fixed.card : Real) + (bankBase.card : Real) +
        ∑ a ∈ candidates, preSelector a := by
  rw [bankPaperCanonicalActualFrozenTotalMass_eq
    D T fixed bankBase candidates preSelector activeSeed H]
  ring

/-! ## Families of literal actual data -/





/-! ## Elementary logarithmic geometry of the literal upper tail -/









/-- Every factor in `(n,2n+h]`, when `h <= n`, has logarithmic displacement
from `log n` between zero and `log 3`. -/
theorem bankPaperCanonicalFactorLog_sub_L_mem_Icc
    {n h a : Nat} (hn : 0 < n) (hh : h <= n)
    (ha : a ∈ factorInterval n (upperEndpoint n h)) :
    Real.log (a : Real) - L n ∈ Set.Icc (0 : Real) (Real.log 3) := by
  have haBounds := Finset.mem_Ioc.mp ha
  have hnLeA : n <= a := haBounds.1.le
  have haLeThree : a <= 3 * n :=
    haBounds.2.trans (upperEndpoint_le_three_mul hh)
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have haReal : 0 < (a : Real) := by
    exact_mod_cast (hn.trans_le hnLeA)
  have hlower : L n <= Real.log (a : Real) := by
    rw [L]
    exact Real.log_le_log hnReal (by exact_mod_cast hnLeA)
  have hupper : Real.log (a : Real) <= Real.log 3 + L n := by
    calc
      Real.log (a : Real) <= Real.log (3 * (n : Real)) :=
        Real.log_le_log haReal (by exact_mod_cast haLeThree)
      _ = Real.log 3 + L n := by
        rw [L, Real.log_mul (by norm_num : (3 : Real) ≠ 0) hnReal.ne']
  exact ⟨sub_nonneg.mpr hlower, by linarith⟩

/-- The literal upper-tail height is `O(secondOrderScale)`. -/
theorem bankPaperCanonicalUpperTailHeight_isBigO
    {c : Real} (hc : 0 < c) :
    bankPaperCanonicalUpperTailHeight c =O[atTop] secondOrderScale := by
  apply IsBigO.of_bound (2 * c)
  filter_upwards [
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
      eventually_secondOrderScale_pos] with n htail hscale
  rw [bankPaperCanonicalUpperTailHeight, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_pos hscale]
  exact htail



/-! ## Centering the literal frozen logarithmic ledger -/

/-- The constructor's coordinatewise dominance makes every literal frozen
remainder nonnegative. -/
theorem bankPaperCanonicalActualFrozenWeight_nonneg
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (a : BankPaperCanonicalActualFrozenIndex candidates) :
    0 <= bankPaperCanonicalActualFrozenWeight
      D candidates preSelector activeSeed a := by
  exact sub_nonneg.mpr
    (bankPaperCanonicalActiveSeedAmbientWeight_le_preSelector H a.2)

/-- Hence the exact total frozen mass is nonnegative. -/
theorem bankPaperCanonicalActualFrozenTotalMass_nonneg
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    0 <= bankPaperCanonicalActualFrozenTotalMass
      D fixed bankBase candidates preSelector activeSeed := by
  unfold bankPaperCanonicalActualFrozenTotalMass
  exact add_nonneg
    (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun a _ha =>
        bankPaperCanonicalActualFrozenWeight_nonneg H a)

/-- Exact centering identity for the literal frozen logarithmic data, valid
at an arbitrary reference logarithm `ell`. -/
theorem bankPaperCanonicalActualFrozenLogMass_sub_total_mul
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real) (ell : Real) :
    bankPaperCanonicalActualFrozenLogMass
          D fixed bankBase candidates preSelector activeSeed -
        bankPaperCanonicalActualFrozenTotalMass
            D fixed bankBase candidates preSelector activeSeed * ell =
      (∑ a ∈ fixed, (Real.log (a : Real) - ell)) +
        (∑ a ∈ bankBase, (Real.log (a : Real) - ell)) +
        ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
          bankPaperCanonicalActualFrozenWeight
              D candidates preSelector activeSeed a *
            (Real.log (bankPaperCanonicalActualFrozenValue a : Real) - ell) := by
  unfold bankPaperCanonicalActualFrozenLogMass
    bankPaperCanonicalActualFrozenTotalMass
  simp only [add_mul, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, mul_sub, Finset.sum_mul]
  ring









/-! ## Exact charged-selector row ledger -/























/-- Losing one further factor of `L` only decreases the paper scale up to an
absolute constant. -/
theorem bankPaperCanonical_secondOrderScale_div_L_isBigO_secondOrderScale :
    (fun n => secondOrderScale n / L n) =O[atTop] secondOrderScale := by
  apply IsBigO.of_bound (1 / Real.log 2)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L n := L_pos (by omega)
  have hscale : 0 < secondOrderScale n := secondOrderScale_pos hn
  have hlogTwoLe : Real.log 2 <= L n := by
    rw [L]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [Real.norm_eq_abs, abs_of_pos (div_pos hscale hL),
    Real.norm_eq_abs, abs_of_pos hscale]
  calc
    secondOrderScale n / L n <=
        secondOrderScale n / Real.log 2 :=
      div_le_div_of_nonneg_left hscale.le hlogTwo hlogTwoLe
    _ = (1 / Real.log 2) * secondOrderScale n := by ring







/-- The selector total-mass estimate already forces the literal frozen mass
to be `O(secondOrderScale)`: the frozen layer is nonnegative and is bounded
by the complete fixed-plus-selector mass. -/
theorem bankPaperCanonicalActualFrozenTotalMassFamily_isBigO
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} (hc : 0 < c)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates preSelector activeSeed =O[atTop]
      secondOrderScale := by
  have HselectorError :
      (fun n => ((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          (∑ a ∈ candidates n, preSelector n a) -
            bankPaperCanonicalUpperTailHeight c n) =O[atTop]
        secondOrderScale :=
    Hselector.trans
      bankPaperCanonical_secondOrderScale_div_L_isBigO_secondOrderScale
  have HselectorMass :
      (fun n => ((fixed n).card : Real) +
        ((bankBase n).card : Real) +
        ∑ a ∈ candidates n, preSelector n a) =O[atTop]
          secondOrderScale :=
    (HselectorError.add (bankPaperCanonicalUpperTailHeight_isBigO hc)).congr_left
      (fun n => by ring)
  have HfrozenLeSelector :
      bankPaperCanonicalActualFrozenTotalMassFamily
          D fixed bankBase candidates preSelector activeSeed =O[atTop]
        (fun n => ((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          ∑ a ∈ candidates n, preSelector n a) := by
    apply IsBigO.of_bound 1
    filter_upwards [Hconstructor] with n hn
    have hm0 : 0 <= bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates preSelector activeSeed n := by
      unfold bankPaperCanonicalActualFrozenTotalMassFamily
      exact bankPaperCanonicalActualFrozenTotalMass_nonneg
        (D := D n) (T := T n) (fixed n) (bankBase n) (candidates n)
          (preSelector n) (activeSeed n) hn
    have hq : 0 <= bankPaperCanonicalLiteralActiveMass
        (D n) (activeSeed n) :=
      (bankPaperCanonicalLiteralActiveMass_pos hn).le
    rw [Real.norm_eq_abs, abs_of_nonneg hm0, one_mul]
    calc
      bankPaperCanonicalActualFrozenTotalMassFamily
            D fixed bankBase candidates preSelector activeSeed n <=
          bankPaperCanonicalActualFrozenTotalMassFamily
              D fixed bankBase candidates preSelector activeSeed n +
            bankPaperCanonicalLiteralActiveMass (D n) (activeSeed n) :=
        le_add_of_nonneg_right hq
      _ = ((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          ∑ a ∈ candidates n, preSelector n a := by
        unfold bankPaperCanonicalActualFrozenTotalMassFamily
        exact bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
          (D n) (T n) (fixed n) (bankBase n) (candidates n) (preSelector n)
            (activeSeed n) hn
      _ <= |((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          ∑ a ∈ candidates n, preSelector n a| := le_abs_self _
      _ = ‖((fixed n).card : Real) +
          ((bankBase n).card : Real) +
          ∑ a ∈ candidates n, preSelector n a‖ :=
        (Real.norm_eq_abs _).symm
  exact HfrozenLeSelector.trans HselectorMass

/-- Interval support and the selector mass estimate automatically center the
literal frozen logarithmic ledger at `m0 * L`. -/
theorem bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {c : Real} (hc : 0 < c)
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates)
    (Hselector : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates preSelector) :
    (fun n =>
      bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector activeSeed n -
        bankPaperCanonicalActualFrozenTotalMassFamily
            D fixed bankBase candidates preSelector activeSeed n * L n) =O[atTop]
      secondOrderScale := by
  have Hm0 := bankPaperCanonicalActualFrozenTotalMassFamily_isBigO
    hc D T fixed bankBase candidates preSelector activeSeed Hconstructor Hselector
  have HcenterByMass :
      (fun n =>
        bankPaperCanonicalActualFrozenLogMassFamily
            D fixed bankBase candidates preSelector activeSeed n -
          bankPaperCanonicalActualFrozenTotalMassFamily
              D fixed bankBase candidates preSelector activeSeed n * L n) =O[atTop]
        (bankPaperCanonicalActualFrozenTotalMassFamily
          D fixed bankBase candidates preSelector activeSeed) := by
    apply IsBigO.of_bound (Real.log 3)
    filter_upwards [Hconstructor, Hgeometry, eventually_gt_atTop 0,
        eventually_upperTailLength_le hc]
        with n hn hgeometry hnPos htail
    have hweight : forall
        a : BankPaperCanonicalActualFrozenIndex (candidates n),
        0 <= bankPaperCanonicalActualFrozenWeight
          (D n) (candidates n) (preSelector n) (activeSeed n) a :=
      fun a => bankPaperCanonicalActualFrozenWeight_nonneg hn a
    have hfixedPoint : ∀ a ∈ fixed n,
        Real.log (a : Real) - L n ∈ Set.Icc (0 : Real) (Real.log 3) := by
      intro a ha
      exact bankPaperCanonicalFactorLog_sub_L_mem_Icc hnPos htail
        (hgeometry.1 ha)
    have hcandidatePoint : forall
        a : BankPaperCanonicalActualFrozenIndex (candidates n),
        Real.log (bankPaperCanonicalActualFrozenValue a : Real) - L n ∈
          Set.Icc (0 : Real) (Real.log 3) := by
      intro a
      simpa only [bankPaperCanonicalActualFrozenValue] using
        (bankPaperCanonicalFactorLog_sub_L_mem_Icc hnPos htail
          (hgeometry.2.2 a.2))
    have hbankBasePoint : ∀ a ∈ bankBase n,
        Real.log (a : Real) - L n ∈ Set.Icc (0 : Real) (Real.log 3) := by
      intro a ha
      exact bankPaperCanonicalFactorLog_sub_L_mem_Icc hnPos htail
        (hgeometry.2.1 ha)
    have hfixedNonneg : 0 <=
        ∑ a ∈ fixed n, (Real.log (a : Real) - L n) := by
      apply Finset.sum_nonneg
      intro a ha
      exact (hfixedPoint a ha).1
    have hbankBaseNonneg : 0 <=
        ∑ a ∈ bankBase n, (Real.log (a : Real) - L n) := by
      apply Finset.sum_nonneg
      intro a ha
      exact (hbankBasePoint a ha).1
    have hcandidateNonneg : 0 <=
        ∑ a : BankPaperCanonicalActualFrozenIndex (candidates n),
          bankPaperCanonicalActualFrozenWeight
              (D n) (candidates n) (preSelector n) (activeSeed n) a *
            (Real.log (bankPaperCanonicalActualFrozenValue a : Real) -
              L n) := by
      apply Finset.sum_nonneg
      intro a _ha
      exact mul_nonneg (hweight a) (hcandidatePoint a).1
    have hcenterNonneg : 0 <=
        bankPaperCanonicalActualFrozenLogMassFamily
            D fixed bankBase candidates preSelector activeSeed n -
          bankPaperCanonicalActualFrozenTotalMassFamily
              D fixed bankBase candidates preSelector activeSeed n * L n := by
      rw [bankPaperCanonicalActualFrozenLogMassFamily,
        bankPaperCanonicalActualFrozenTotalMassFamily,
        bankPaperCanonicalActualFrozenLogMass_sub_total_mul]
      exact add_nonneg (add_nonneg hfixedNonneg hbankBaseNonneg)
        hcandidateNonneg
    have hm0 : 0 <= bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates preSelector activeSeed n := by
      unfold bankPaperCanonicalActualFrozenTotalMassFamily
      exact bankPaperCanonicalActualFrozenTotalMass_nonneg
        (D := D n) (T := T n) (fixed n) (bankBase n) (candidates n)
          (preSelector n) (activeSeed n) hn
    rw [Real.norm_eq_abs, abs_of_nonneg hcenterNonneg,
      Real.norm_eq_abs, abs_of_nonneg hm0,
      bankPaperCanonicalActualFrozenLogMassFamily,
      bankPaperCanonicalActualFrozenTotalMassFamily,
      bankPaperCanonicalActualFrozenLogMass_sub_total_mul]
    calc
      (∑ a ∈ fixed n, (Real.log (a : Real) - L n)) +
          (∑ a ∈ bankBase n, (Real.log (a : Real) - L n)) +
          ∑ a : BankPaperCanonicalActualFrozenIndex (candidates n),
            bankPaperCanonicalActualFrozenWeight
                (D n) (candidates n) (preSelector n) (activeSeed n) a *
              (Real.log (bankPaperCanonicalActualFrozenValue a : Real) -
                L n) <=
        (∑ _a ∈ fixed n, Real.log 3) +
          (∑ _a ∈ bankBase n, Real.log 3) +
          ∑ a : BankPaperCanonicalActualFrozenIndex (candidates n),
            bankPaperCanonicalActualFrozenWeight
                (D n) (candidates n) (preSelector n) (activeSeed n) a *
              Real.log 3 := by
        apply add_le_add
        · apply add_le_add
          · apply Finset.sum_le_sum
            intro a ha
            exact (hfixedPoint a ha).2
          · apply Finset.sum_le_sum
            intro a ha
            exact (hbankBasePoint a ha).2
        · apply Finset.sum_le_sum
          intro a _ha
          exact mul_le_mul_of_nonneg_left (hcandidatePoint a).2 (hweight a)
      _ = bankPaperCanonicalActualFrozenTotalMass
          (D n) (fixed n) (bankBase n) (candidates n) (preSelector n)
            (activeSeed n) *
            Real.log 3 := by
        unfold bankPaperCanonicalActualFrozenTotalMass
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.sum_mul]
        ring
      _ = Real.log 3 * bankPaperCanonicalActualFrozenTotalMass
          (D n) (fixed n) (bankBase n) (candidates n) (preSelector n)
            (activeSeed n) := by
        ring
  exact HcenterByMass.trans Hm0

/-! ## The remaining actual analytic sources -/

















/-! ## Construction of the old Section 8 ledger -/













end

end Erdos390.WholePaper

end

universe u_1
theorem solution :
∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : Nonempty.{u_1 + 1} Head] {c : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
    ∀ (D : Nat → @Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head inst)
      (T : (n : Nat) → @Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1} Head inst (D n))
      (fixed bankBase candidates : Nat → Finset.{0} Nat) (preSelector : Nat → Nat → Real)
      (activeSeed : (n : Nat) → @Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst (D n) → Real),
      @Filter.Eventually.{0} Nat
          (fun (n : Nat) =>
            @Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstructor.{u_1} Head inst inst_1 (D n) (T n)
              (candidates n) (preSelector n) (activeSeed n))
          (@Filter.atTop.{0} Nat Nat.instPreorder) →
        @Erdos390.WholePaper.BankPaperCanonicalActualFrozenIntervalGeometry c fixed bankBase candidates →
          Erdos390.WholePaper.BankPaperCanonicalActualSelectorMassEstimate c fixed bankBase candidates preSelector →
            @Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm (@Filter.atTop.{0} Nat Nat.instPreorder)
              (fun (n : Nat) =>
                @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Erdos390.WholePaper.bankPaperCanonicalActualFrozenLogMassFamily.{u_1} Head inst D fixed bankBase
                    candidates preSelector activeSeed n)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Erdos390.WholePaper.bankPaperCanonicalActualFrozenTotalMassFamily.{u_1} Head inst D fixed bankBase
                      candidates preSelector activeSeed n)
                    (Erdos390.Full.Scale.L n)))
              Erdos390.WholePaper.secondOrderScale := by
  exact @Erdos390.WholePaper.bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO
