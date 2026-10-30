-- Prove2me | solution 1 for Blocks3HAdmissible.blocks3_number_over_factorial_thirdOrder_saddle
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T02:49:44.197326+00:00
-- url     : https://prove2.me/submissions/d5cb766f-2d2b-4eeb-a803-1e2a00af536c

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Exp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bell
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3SecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Blocks3ThirdOrder
import Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_egf_set
import Theorems.Thm_coeff_thirdOrder_saddle
import Mathlib
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

@[simp] lemma coeff_toFMLS (f : PowerSeries ℂ) (n : ℕ) :
    (toFMLS f).coeff n = PowerSeries.coeff (R := ℂ) n f := by
  simp [toFMLS]

@[simp] lemma nnnorm_toFMLS_apply (f : PowerSeries ℂ) (n : ℕ) :
    ‖toFMLS f n‖₊ = ‖PowerSeries.coeff (R := ℂ) n f‖₊ := by
  apply NNReal.eq
  simp [toFMLS]

end PowerSeries
end
end

section
open scoped BigOperators PowerSeries
open List Finset

noncomputable section

namespace FormalMultilinearSeries

lemma ofScalars_comp_coeff (a b : ℕ → ℂ) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ a).comp
      (FormalMultilinearSeries.ofScalars ℂ b)).coeff n =
      ∑ c : Composition n, a c.length * ∏ i : Fin c.length, b (c.blocksFun i) := by
  rw [FormalMultilinearSeries.coeff]
  simp [FormalMultilinearSeries.comp, FormalMultilinearSeries.applyComposition,
    FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn, smul_eq_mul]

end FormalMultilinearSeries

private lemma prod_coeff_eq_zero_of_not_pos {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0)
    {d n : ℕ} (l : { l : Fin d → ℕ // ∑ i, l i = n })
    (hl : ¬ ∀ i, 0 < l.1 i) :
    (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) = 0 := by
  classical
  push Not at hl
  rcases hl with ⟨i, hi⟩
  have hzero : l.1 i = 0 := Nat.eq_zero_of_le_zero hi
  rw [Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [hzero]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg

private lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero
    {g : ℂ⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    {n d : ℕ} (hnd : n < d) :
    PowerSeries.coeff n (g ^ d) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    exact PowerSeries.coeff_of_lt_order n
      (lt_of_lt_of_le (by exact_mod_cast hnd)
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg))

private lemma coeff_pow_eq_sum_composition_length {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (d n : ℕ) :
    PowerSeries.coeff n (g ^ d) =
      ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
  classical
  rw [PowerSeries.coeff_pow]
  let A := (Finset.range d).finsuppAntidiag n
  let B := { l : Fin d → ℕ // ∑ i, l i = n }
  letI : Fintype B := Fintype.ofEquiv A (finsuppAntidiagRangeEquivFin n d)
  let P : B → Prop := fun l => ∀ i, 0 < l.1 i
  let Pos := { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n }
  letI : Fintype Pos := Fintype.ofEquiv { x : B // P x } (positiveSubtypeEquiv n d)
  have h_antidiag_to_B :
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
        ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
    calc
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
          ∑ a : A, ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g := by
        simpa [A] using (Finset.sum_attach A
          (fun a : ℕ →₀ ℕ => ∏ i ∈ Finset.range d, PowerSeries.coeff (a i) g)).symm
      _ = ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
        exact Fintype.sum_equiv (finsuppAntidiagRangeEquivFin n d)
          (fun a : A => ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g)
          (fun l : B => ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
          (by
            intro a
            calc
              (∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g) =
                  ∏ i : Fin d, PowerSeries.coeff (a.1 i.val) g := by
                exact (Fin.prod_univ_eq_prod_range
                  (fun i => PowerSeries.coeff (a.1 i) g) d).symm
              _ = ∏ i : Fin d,
                    PowerSeries.coeff (((finsuppAntidiagRangeEquivFin n d) a).1 i) g := by
                simp [finsuppAntidiagRangeEquivFin])
  rw [h_antidiag_to_B]
  have h_filter :
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
        ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
    have hsubset : (Finset.univ.filter P) ⊆ (Finset.univ : Finset B) := by
      intro x _hx
      simp
    have hsum_subset :
        ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) =
          ∑ x : B, ∏ i : Fin d, PowerSeries.coeff (x.1 i) g := by
      refine Finset.sum_subset hsubset ?_
      intro x _hx hxnot
      exact prod_coeff_eq_zero_of_not_pos hg x (by simpa [P] using hxnot)
    calc
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
          ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) :=
        hsum_subset.symm
      _ = ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
        refine Finset.sum_subtype (Finset.univ.filter P) ?_
          (fun x : B => ∏ i : Fin d, PowerSeries.coeff (x.1 i) g)
        intro x
        simp [P]
  rw [h_filter]
  calc
    (∑ l : { x : B // P x },
        ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g) =
      ∑ l : Pos,
        ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
      exact Fintype.sum_equiv (positiveSubtypeEquiv n d)
        (fun l : { x : B // P x } =>
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (by intro l; rfl)
    _ = ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      exact Fintype.sum_equiv (positiveFinTupleCompositionEquiv n d)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (fun c : { c : Composition n // c.length = d } =>
          ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g)
        (by
          intro l
          change (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
            ∏ i : Fin (List.ofFn l.1).length,
              PowerSeries.coeff ((List.ofFn l.1).get i) g
          exact Fintype.prod_equiv (finCongr (by simp [List.length_ofFn]))
            (fun i : Fin d => PowerSeries.coeff (l.1 i) g)
            (fun i : Fin (List.ofFn l.1).length =>
              PowerSeries.coeff ((List.ofFn l.1).get i) g)
            (by intro i; simp))

private lemma subst_coeff_eq_sum_composition {f g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst g) =
      ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
  classical
  have hsubst := PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hg) f n
  rw [hsubst]
  simp only [smul_eq_mul]
  let term : ℕ → ℂ := fun d => PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)
  have hsupport : Function.support term ⊆ (Finset.range (n + 1) : Set ℕ) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hmem
    have hnd : n < d := by omega
    have hz : PowerSeries.coeff n (g ^ d) = 0 :=
      coeff_pow_eq_zero_of_constantCoeff_eq_zero hg hnd
    have hdne : term d ≠ 0 := hd
    simp [term, hz] at hdne
  calc
    (∑ᶠ d : ℕ, PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) =
        ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) := by
      simpa [term] using finsum_eq_sum_of_support_subset term hsupport
    _ = ∑ d ∈ Finset.range (n + 1),
        ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      refine Finset.sum_congr rfl ?_
      intro d _hd
      rw [coeff_pow_eq_sum_composition_length hg d n]
      simp [Finset.mul_sum]
    _ = ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun d => ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g) (n + 1)]
      rw [← Fintype.sum_sigma (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
        PowerSeries.coeff x.1.val f *
          ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)]
      exact Fintype.sum_equiv (sigmaLengthCompositionEquiv n)
        (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
          PowerSeries.coeff x.1.val f *
            ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)
        (fun c : Composition n =>
          PowerSeries.coeff c.length f *
            ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g)
        (by
          intro x
          rcases x with ⟨d, c, hc⟩
          dsimp [sigmaLengthCompositionEquiv]
          apply congrArg₂ HMul.hMul
          · exact congrArg (fun k => PowerSeries.coeff k f) hc.symm
          · rfl)

namespace PowerSeries

theorem toFMLS_subst_eq_comp {f g : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.toFMLS (f.subst g) =
      (PowerSeries.toFMLS f).comp (PowerSeries.toFMLS g) := by
  ext n
  simp [PowerSeries.coeff_toFMLS]
  change PowerSeries.coeff n (f.subst g) =
    ((FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n f)).comp
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n g))).coeff n
  rw [FormalMultilinearSeries.ofScalars_comp_coeff]
  exact subst_coeff_eq_sum_composition hg n

end PowerSeries
end
end

section
open Complex
open scoped NNReal ENNReal

noncomputable section

theorem expCarrier_toFMLS_eq_expSeries :
    PowerSeries.toFMLS expCarrier = NormedSpace.expSeries ℂ ℂ := by
  rw [NormedSpace.expSeries_eq_ofScalars]
  ext n
  simp [PowerSeries.toFMLS, expCarrier]

@[simp] theorem expCarrier_radius :
    (PowerSeries.toFMLS expCarrier).radius = ⊤ := by
  rw [expCarrier_toFMLS_eq_expSeries]
  exact NormedSpace.expSeries_radius_eq_top ℂ ℂ

end
end

section
/-!
# The exponential saddle testbed

This file instantiates the saddle assembly machinery for `f z = exp z`.
The hard local-analysis estimates are isolated as explicitly documented
lemmas: the second-order exponential limit, the central domination estimate,
and the tail estimate.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

namespace ExpStirling

lemma expCarrier_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS expCarrier) (0 : ℂ) := by
  simpa [expSeriesC] using
    (show HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS expCarrier) (0 : ℂ) by
      simpa [_root_.expCarrier_toFMLS_eq_expSeries] using exp_hasFPowerSeriesAt_zero)

end ExpStirling
end
end

section
/-!
# Involution H-admissible saddle data

This file records the Hayman data for the involution EGF
`exp (z + z^2 / 2)`.  The saddle data are
`a(r)=r+r^2`, `b(r)=r+2r^2`, and `δ(r)=r^(-3/4)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace InvolutionHAdmissible

/-- The genuine complex EGF carrier coming from the Ch2 involution class. -/
def involCarrier : PowerSeries ℂ :=
  PowerSeries.mapℂ AnalyticCombinatorics.Ch1.CombClass.parts12.set.egf

@[simp] theorem involCarrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n involCarrier = (involCoeffR n : ℂ) := by
  simp [involCarrier, involCoeffR, AnalyticCombinatorics.Ch1.CombClass.coeff_egf]

lemma hasFPowerSeriesAt_id_toFMLS_X :
    HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n • (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)).coeff n
  have hsingle : HasSum term (term 1) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

lemma hasFPowerSeriesAt_mul_toFMLS {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasFPowerSeriesAt f (PowerSeries.toFMLS F) (0 : ℂ))
    (hg : HasFPowerSeriesAt g (PowerSeries.toFMLS G) (0 : ℂ)) :
    HasFPowerSeriesAt (fun z : ℂ => f z * g z)
      (PowerSeries.toFMLS (F * G)) (0 : ℂ) := by
  rcases hf with ⟨rf, hrf⟩
  rcases hg with ⟨rg, hrg⟩
  rw [hasFPowerSeriesAt_iff]
  refine eventually_of_mem
    (Metric.eball_mem_nhds (0 : ℂ) (lt_min hrf.r_pos hrg.r_pos)) ?_
  intro z hz
  have hzf : z ∈ Metric.eball (0 : ℂ) rf := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_left _ _))
  have hzg : z ∈ Metric.eball (0 : ℂ) rg := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_right _ _))
  let a : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n F
  let b : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n G
  have hsumf : HasSum a (f z) := by
    have h := hrf.hasSum hzf
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hsumg : HasSum b (g z) := by
    have h := hrg.hasSum hzg
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hzfrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS F).radius :=
    Metric.eball_subset_eball hrf.r_le hzf
  have hzgrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS G).radius :=
    Metric.eball_subset_eball hrg.r_le hzg
  have hnormf : Summable fun n : ℕ => ‖a n‖ := by
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS F).summable_norm_apply hzfrad
  have hnormg : Summable fun n : ℕ => ‖b n‖ := by
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS G).summable_norm_apply hzgrad
  let cseq : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n (F * G)
  let d : ℕ → ℂ := fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
  have hcd : ∀ n, cseq n = d n := by
    intro n
    change z ^ n * PowerSeries.coeff (R := ℂ) n (F * G) =
      ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro kl hkl
    have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    simp [a, b]
    rw [← hsum, pow_add]
    ring
  have hnormd : Summable fun n : ℕ => ‖d n‖ := by
    simpa [d] using summable_norm_sum_mul_antidiagonal_of_summable_norm hnormf hnormg
  have hnormc : Summable fun n : ℕ => ‖cseq n‖ := by
    exact hnormd.congr (fun n => by rw [hcd n])
  have hsumc : Summable cseq := hnormc.of_norm
  have htsum : (∑' n : ℕ, cseq n) = f z * g z := by
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnormf hnormg
    rw [hsumf.tsum_eq, hsumg.tsum_eq] at hprod
    rw [tsum_congr hcd, ← hprod]
  have hmain : HasSum cseq (f z * g z) := hsumc.hasSum_iff.mpr htsum
  simpa [cseq, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hmain

/-- Continuous involution saddle mean, `a(r)=r+r^2`. -/
def involSaddleAReal (r : ℝ) : ℝ :=
  r + r ^ 2

/-- Hayman window for the involution saddle. -/
def involSaddleDeltaReal (r : ℝ) : ℝ :=
  r ^ (-(3 / 4 : ℝ))

@[simp] lemma involSaddleAReal_apply (r : ℝ) :
    involSaddleAReal r = r + r ^ 2 := rfl

@[simp] lemma involSaddleBReal_apply (r : ℝ) :
    involSaddleBReal r = r + 2 * r ^ 2 := rfl

@[simp] lemma involSaddleDeltaReal_apply (r : ℝ) :
    involSaddleDeltaReal r = r ^ (-(3 / 4 : ℝ)) := rfl

end InvolutionHAdmissible
end
end

section
/-!
# Blocks of size at most three: H-admissible saddle data

This file records the Hayman data for the EGF
`exp (z + z^2/2 + z^3/6)`, the labelled SET class whose components have
sizes `1`, `2`, or `3`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.counts_parts123 (n : ℕ) :
    CombClass.parts123.counts n =
      if n = 1 then 1 else if n = 2 then 1 else if n = 3 then 1 else 0 :=
  Fintype.card_fin _

/-- The EGF of the size-`1`, `2`, `3` component class is `z + z^2/2 + z^3/6`. -/
theorem CombClass.egf_parts123_egf :
    CombClass.parts123.egf =
      X + (2⁻¹ : ℚ) • X ^ 2 + (6⁻¹ : ℚ) • X ^ 3 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_parts123, map_add, map_add, coeff_X,
    map_smul, map_smul, coeff_X_pow, coeff_X_pow, smul_eq_mul, smul_eq_mul]
  by_cases h1 : n = 1
  · subst n
    norm_num [Nat.factorial]
  by_cases h2 : n = 2
  · subst n
    norm_num [Nat.factorial]
  by_cases h3 : n = 3
  · subst n
    norm_num [Nat.factorial]
  simp [h1, h2, h3]

/-- The EGF of set partitions into blocks of size at most `3`. -/
theorem CombClass.egf_blocks3 :
    CombClass.blocks3.egf =
      (PowerSeries.exp ℚ).subst
        (X + (2⁻¹ : ℚ) • X ^ 2 + (6⁻¹ : ℚ) • X ^ 3) := by
  rw [CombClass.egf_set _ (by simp [CombClass.counts_parts123]),
    CombClass.egf_parts123_egf]

end AnalyticCombinatorics.Ch1

namespace Blocks3HAdmissible

/-- The genuine complex EGF carrier from the Ch2 labelled SET construction. -/
def blocks3Carrier : PowerSeries ℂ :=
  PowerSeries.mapℂ AnalyticCombinatorics.Ch1.CombClass.blocks3.egf

@[simp] theorem blocks3Carrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n blocks3Carrier = (blocks3CoeffR n : ℂ) := by
  simp [blocks3Carrier, blocks3CoeffR, AnalyticCombinatorics.Ch1.CombClass.coeff_egf]

/-- The formal series used by the H-admissible interface. -/
noncomputable abbrev blocks3Series : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS blocks3Carrier

/-- The cubic inner PowerSeries `z + z^2/2 + z^3/6`. -/
def blocks3InnerPS : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) +
    (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2 +
      (6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3

lemma blocks3InnerPS_constantCoeff : PowerSeries.constantCoeff blocks3InnerPS = 0 := by
  unfold blocks3InnerPS
  have hX : PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ) = 0 :=
    _root_.PowerSeries.constantCoeff_X
  have hpow2 : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) =
      (PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ)) ^ 2 :=
    _root_.map_pow (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) 2
  have hpow2zero : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) = 0 :=
    hpow2.trans ((congrArg (fun z : ℂ => z ^ 2) hX).trans (by norm_num))
  have hsmul2 : PowerSeries.constantCoeff (R := ℂ)
      ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) =
        (2⁻¹ : ℂ) • PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) :=
    _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℂ) ^ 2) (2⁻¹ : ℂ)
  have hsmul2zero : PowerSeries.constantCoeff (R := ℂ)
      ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) = 0 :=
    hsmul2.trans ((congrArg (fun z : ℂ => (2⁻¹ : ℂ) • z) hpow2zero).trans (smul_zero _))
  have hpow3 : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 3) =
      (PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ)) ^ 3 :=
    _root_.map_pow (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) 3
  have hpow3zero : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 3) = 0 :=
    hpow3.trans ((congrArg (fun z : ℂ => z ^ 3) hX).trans (by norm_num))
  have hsmul3 : PowerSeries.constantCoeff (R := ℂ)
      ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3) =
        (6⁻¹ : ℂ) • PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 3) :=
    _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℂ) ^ 3) (6⁻¹ : ℂ)
  have hsmul3zero : PowerSeries.constantCoeff (R := ℂ)
      ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3) = 0 :=
    hsmul3.trans ((congrArg (fun z : ℂ => (6⁻¹ : ℂ) • z) hpow3zero).trans (smul_zero _))
  have hadd2 : (PowerSeries.constantCoeff (R := ℂ)) ((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) = (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) + (PowerSeries.constantCoeff (R := ℂ)) ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) :=
    _root_.map_add (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)
  have hadd2zero : (PowerSeries.constantCoeff (R := ℂ)) ((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) = 0 :=
    hadd2.trans ((congrArg₂ (fun x y : ℂ => x + y) hX hsmul2zero).trans (add_zero (0 : ℂ)))
  have hadd3 : (PowerSeries.constantCoeff (R := ℂ)) (((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) + ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3)) =
      (PowerSeries.constantCoeff (R := ℂ)) ((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) + (PowerSeries.constantCoeff (R := ℂ)) ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3) :=
    _root_.map_add (PowerSeries.constantCoeff (R := ℂ)) ((PowerSeries.X : PowerSeries ℂ) + ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)) ((6⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 3)
  exact hadd3.trans
    ((congrArg₂ (fun x y : ℂ => x + y) hadd2zero hsmul3zero).trans (add_zero (0 : ℂ)))

theorem blocks3Carrier_eq_complex_subst :
    blocks3Carrier = (PowerSeries.exp ℂ).subst blocks3InnerPS := by
  rw [blocks3Carrier, AnalyticCombinatorics.Ch1.CombClass.egf_blocks3]
  have hsubst : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℚ) +
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
          (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    have hX : PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ) = 0 :=
      _root_.PowerSeries.constantCoeff_X
    have hpow2 : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) =
        (PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ)) ^ 2 :=
      _root_.map_pow (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) 2
    have hpow2zero : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) = 0 :=
      hpow2.trans ((congrArg (fun z : ℚ => z ^ 2) hX).trans (by norm_num))
    have hsmul2 : PowerSeries.constantCoeff (R := ℚ)
        ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) =
          (2⁻¹ : ℚ) • PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) :=
      _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℚ) ^ 2) (2⁻¹ : ℚ)
    have hsmul2zero : PowerSeries.constantCoeff (R := ℚ)
        ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) = 0 :=
      hsmul2.trans ((congrArg (fun z : ℚ => (2⁻¹ : ℚ) • z) hpow2zero).trans (smul_zero _))
    have hpow3 : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 3) =
        (PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ)) ^ 3 :=
      _root_.map_pow (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) 3
    have hpow3zero : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 3) = 0 :=
      hpow3.trans ((congrArg (fun z : ℚ => z ^ 3) hX).trans (by norm_num))
    have hsmul3 : PowerSeries.constantCoeff (R := ℚ)
        ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3) =
          (6⁻¹ : ℚ) • PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 3) :=
      _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℚ) ^ 3) (6⁻¹ : ℚ)
    have hsmul3zero : PowerSeries.constantCoeff (R := ℚ)
        ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3) = 0 :=
      hsmul3.trans ((congrArg (fun z : ℚ => (6⁻¹ : ℚ) • z) hpow3zero).trans (smul_zero _))
    have hadd2 : (PowerSeries.constantCoeff (R := ℚ)) ((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) = (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) + (PowerSeries.constantCoeff (R := ℚ)) ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) :=
      _root_.map_add (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)
    have hadd2zero : (PowerSeries.constantCoeff (R := ℚ)) ((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) = 0 :=
      hadd2.trans ((congrArg₂ (fun x y : ℚ => x + y) hX hsmul2zero).trans (add_zero (0 : ℚ)))
    have hadd3 : (PowerSeries.constantCoeff (R := ℚ)) (((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) + ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3)) =
        (PowerSeries.constantCoeff (R := ℚ)) ((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) + (PowerSeries.constantCoeff (R := ℚ)) ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3) :=
      _root_.map_add (PowerSeries.constantCoeff (R := ℚ)) ((PowerSeries.X : PowerSeries ℚ) + ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)) ((6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3)
    exact hadd3.trans
      ((congrArg₂ (fun x y : ℚ => x + y) hadd2zero hsmul3zero).trans (add_zero (0 : ℚ)))
  have hmap_inner :
      (((PowerSeries.X : PowerSeries ℚ) +
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
            (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3).map
          (algebraMap ℚ ℂ)) =
        blocks3InnerPS := by
    ext n
    by_cases h1 : n = 1
    · subst n
      norm_num [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
      change (1 : ℂ) = ((1 : ℂ) + 0) + 0
      exact ((add_zero ((1 : ℂ) + 0)).trans (add_zero (1 : ℂ))).symm
    by_cases h2 : n = 2
    · subst n
      norm_num [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
      change (0 : ℂ) = (0 : ℂ)
      rfl
    by_cases h3 : n = 3
    · subst n
      norm_num [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
      change (0 : ℂ) = (0 : ℂ)
      rfl
    simp [blocks3InnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow, h2, h3,
      add_assoc]
  have hmap_exp :
      (PowerSeries.exp ℚ).map (algebraMap ℚ ℂ) = PowerSeries.exp ℂ := by
    ext n
    simp
  change (((PowerSeries.exp ℚ).subst
        ((PowerSeries.X : PowerSeries ℚ) +
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
            (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3)).map
      (algebraMap ℚ ℂ)) = _
  rw [PowerSeries.map_subst
    (a := ((PowerSeries.X : PowerSeries ℚ) +
      (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
        (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3))
    (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ)]
  rw [hmap_exp]
  change (PowerSeries.exp ℂ).subst
      ((((PowerSeries.X : PowerSeries ℚ) +
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 +
          (6⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 3).map
          (algebraMap ℚ ℂ))) =
    (PowerSeries.exp ℂ).subst blocks3InnerPS
  rw [hmap_inner]

lemma blocks3Inner_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => z + z ^ 2 / 2 + z ^ 3 / 6)
      (PowerSeries.toFMLS blocks3InnerPS) (0 : ℂ) := by
  have hX : HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) :=
    InvolutionHAdmissible.hasFPowerSeriesAt_id_toFMLS_X
  have hX2 : HasFPowerSeriesAt (fun z : ℂ => z * z)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using InvolutionHAdmissible.hasFPowerSeriesAt_mul_toFMLS hX hX
  have hX3 : HasFPowerSeriesAt (fun z : ℂ => (z * z) * z)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 3)) (0 : ℂ) := by
    have hmul := InvolutionHAdmissible.hasFPowerSeriesAt_mul_toFMLS hX2 hX
    simpa [pow_succ, pow_two, mul_assoc] using hmul
  have hhalf : HasFPowerSeriesAt (fun z : ℂ => (2⁻¹ : ℂ) • (z * z))
      ((2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2))
      (0 : ℂ) := by
    simpa using (HasFPowerSeriesAt.const_smul (c := (2⁻¹ : ℂ)) hX2)
  have hsixth : HasFPowerSeriesAt (fun z : ℂ => (6⁻¹ : ℂ) • ((z * z) * z))
      ((6⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 3))
      (0 : ℂ) := by
    simpa using (HasFPowerSeriesAt.const_smul (c := (6⁻¹ : ℂ)) hX3)
  have hsum := (hX.add hhalf).add hsixth
  have hseries :
      PowerSeries.toFMLS blocks3InnerPS =
        PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ) +
          (2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2) +
            (6⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 3) := by
    ext n
    simp [blocks3InnerPS, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]
  rw [hseries]
  convert hsum using 1
  funext z
  simp [smul_eq_mul]
  ring_nf

lemma blocks3Fun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt blocks3Fun blocks3Series (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS (PowerSeries.exp ℂ))
      ((fun z : ℂ => z + z ^ 2 / 2 + z ^ 3 / 6) 0) := by
    simpa using ExpStirling.expCarrier_hasFPowerSeriesAt_zero
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => z + z ^ 2 / 2 + z ^ 3 / 6)
    houter blocks3Inner_hasFPowerSeriesAt_zero
  change HasFPowerSeriesAt blocks3Fun (PowerSeries.toFMLS blocks3Carrier) (0 : ℂ)
  rw [blocks3Carrier_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp blocks3InnerPS_constantCoeff]
  simpa [Function.comp_def, blocks3Fun, blocks3Series] using hcomp

/-- Hayman window for the cubic polynomial saddle. -/
def blocks3SaddleDeltaReal (r : ℝ) : ℝ :=
  r ^ (-(7 / 6 : ℝ))

@[simp] lemma blocks3SaddleAReal_apply (r : ℝ) :
    blocks3SaddleAReal r = r + r ^ 2 + r ^ 3 / 2 := rfl

@[simp] lemma blocks3SaddleBReal_apply (r : ℝ) :
    blocks3SaddleBReal r = r + 2 * r ^ 2 + 3 * r ^ 3 / 2 := rfl

@[simp] lemma blocks3SaddleDeltaReal_apply (r : ℝ) :
    blocks3SaddleDeltaReal r = r ^ (-(7 / 6 : ℝ)) := rfl

/-- The exact exponent left after removing the linear and quadratic saddle terms. -/
def blocks3LocalExponent (r θ : ℝ) : ℂ :=
  (r : ℂ) * ExpStirling.expLocalRemainder θ +
    (((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ)) +
      (((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))

lemma complex_two_mul_theta_I (θ : ℝ) :
    (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
      ((2 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma complex_three_mul_theta_I (θ : ℝ) :
    (((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
      ((3 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma blocks3_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r θ =
      Complex.exp (blocks3LocalExponent r θ) := by
  unfold saddleLocalRatio blocks3Fun blocks3LocalExponent blocks3SaddleAReal blocks3SaddleBReal
  have hsq_full :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
        ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
    rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
        ((2 * θ : ℝ) : ℂ) * Complex.I by
      simpa using complex_two_mul_theta_I θ]
  have hcube_full :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3 =
        ((r ^ 3 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show (r : ℂ) ^ 3 = ((r ^ 3 : ℝ) : ℂ) by norm_num]
    rw [show (((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
        ((3 * θ : ℝ) : ℂ) * Complex.I by
      simpa using complex_three_mul_theta_I θ]
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  rw [ExpStirling.expLocalRemainder_eq θ]
  rw [ExpStirling.expLocalRemainder_eq (2 * θ)]
  rw [ExpStirling.expLocalRemainder_eq (3 * θ)]
  rw [hsq_full, hcube_full]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow]
  ring_nf

lemma blocks3_f_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < (blocks3Fun (r : ℂ)).re := by
  refine Eventually.of_forall fun r => ?_
  unfold blocks3Fun
  have harg :
      (r : ℂ) + (r : ℂ) ^ 2 / 2 + (r : ℂ) ^ 3 / 6 =
        ((r + r ^ 2 / 2 + r ^ 3 / 6 : ℝ) : ℂ) := by
    norm_num
  have hval :
      Complex.exp (((r + r ^ 2 / 2 + r ^ 3 / 6 : ℝ) : ℂ)) =
        ((Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) : ℝ) : ℂ) := by
    simp
  rw [harg, hval]
  exact Real.exp_pos (r + r ^ 2 / 2 + r ^ 3 / 6)

lemma blocks3_b_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < blocks3SaddleBReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold blocks3SaddleBReal
  positivity

lemma blocks3_delta_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < blocks3SaddleDeltaReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold blocks3SaddleDeltaReal
  exact Real.rpow_pos_of_pos hr _

lemma blocks3_delta_tendsto_zero :
    Tendsto blocks3SaddleDeltaReal atTop (𝓝 0) := by
  simpa [blocks3SaddleDeltaReal] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6))

lemma blocks3_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in atTop, blocks3SaddleDeltaReal r ≤ Real.pi :=
  blocks3_delta_tendsto_zero.eventually_le_const Real.pi_pos

lemma blocks3_delta_le_one_eventually :
    ∀ᶠ r : ℝ in atTop, blocks3SaddleDeltaReal r ≤ 1 :=
  blocks3_delta_tendsto_zero.eventually_le_const zero_lt_one

lemma blocks3_delta_mul_rpow_three_halves_eventually :
    (fun r : ℝ => blocks3SaddleDeltaReal r * r ^ (3 / 2 : ℝ)) =ᶠ[atTop]
      fun r : ℝ => r ^ (1 / 3 : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  calc
    blocks3SaddleDeltaReal r * r ^ (3 / 2 : ℝ)
        = r ^ (-(7 / 6 : ℝ)) * r ^ (3 / 2 : ℝ) := by
          simp [blocks3SaddleDeltaReal]
    _ = r ^ (-(7 / 6 : ℝ) + (3 / 2 : ℝ)) := by
          rw [Real.rpow_add hr]
    _ = r ^ (1 / 3 : ℝ) := by norm_num

lemma blocks3_delta_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))
      atTop atTop := by
  have hpow : Tendsto (fun r : ℝ => r ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    blocks3_delta_mul_rpow_three_halves_eventually] with r hr heq
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hb_ge : r ^ 3 ≤ blocks3SaddleBReal r := by
    unfold blocks3SaddleBReal
    nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) hr0]
  have hrpow_sq : (r ^ (3 / 2 : ℝ)) ^ 2 = r ^ 3 := by
    calc
      (r ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = r ^ ((3 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hr0 (3 / 2 : ℝ) 2).symm
      _ = r ^ (3 : ℝ) :=
        congrArg (fun e : ℝ => r ^ e) (by norm_num : (3 / 2 : ℝ) * 2 = 3)
      _ = r ^ (3 : ℕ) := Real.rpow_natCast r 3
  have hsqrt_ge : r ^ (3 / 2 : ℝ) ≤ Real.sqrt (blocks3SaddleBReal r) := by
    exact Real.le_sqrt_of_sq_le (by simpa [hrpow_sq] using hb_ge)
  have hδ_nonneg : 0 ≤ blocks3SaddleDeltaReal r := by
    unfold blocks3SaddleDeltaReal
    positivity
  calc
    r ^ (1 / 3 : ℝ) =
        blocks3SaddleDeltaReal r * r ^ (3 / 2 : ℝ) := heq.symm
    _ ≤ blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r) :=
      mul_le_mul_of_nonneg_left hsqrt_ge hδ_nonneg

lemma blocks3_differentiableOn_eventually :
    ∀ᶠ r : ℝ in atTop,
      DifferentiableOn ℂ blocks3Fun (Metric.closedBall (0 : ℂ) r) := by
  refine Eventually.of_forall fun r => ?_
  unfold blocks3Fun
  fun_prop

def blocks3LocalControl (r : ℝ) : ℝ :=
  r ^ 3 * (blocks3SaddleDeltaReal r) ^ 3

lemma blocks3LocalControl_eq_rpow_eventually :
    blocks3LocalControl =ᶠ[atTop] fun r : ℝ => r ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hr0 : 0 ≤ r := hr.le
  have hr3_rpow : r ^ 3 = r ^ (3 : ℝ) := by
    exact (Real.rpow_natCast r 3).symm
  have hdelta_pow :
      (r ^ (-(7 / 6 : ℝ))) ^ 3 = r ^ (-(7 / 6 : ℝ) * (3 : ℝ)) :=
    (Real.rpow_mul_natCast hr0 (-(7 / 6 : ℝ)) 3).symm
  unfold blocks3LocalControl blocks3SaddleDeltaReal
  calc
    r ^ 3 * (r ^ (-(7 / 6 : ℝ))) ^ 3
        = r ^ (3 : ℝ) * r ^ (-(7 / 6 : ℝ) * (3 : ℝ)) := by
          rw [hr3_rpow, hdelta_pow]
    _ = r ^ ((3 : ℝ) + (-(7 / 6 : ℝ) * (3 : ℝ))) := by
          rw [Real.rpow_add hr]
    _ = r ^ (-(1 / 2 : ℝ)) := by norm_num

lemma blocks3LocalControl_tendsto_zero :
    Tendsto blocks3LocalControl atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  exact Tendsto.congr' blocks3LocalControl_eq_rpow_eventually.symm hpow

def blocks3LocalConstant : ℝ :=
  100 * Real.exp 3

lemma blocks3LocalBound_tendsto_zero :
    Tendsto (fun r : ℝ => blocks3LocalConstant * blocks3LocalControl r) atTop (𝓝 0) := by
  simpa using blocks3LocalControl_tendsto_zero.const_mul blocks3LocalConstant

lemma expLocalRemainder_norm_le_exp_three {θ : ℝ} (hθ : |θ| ≤ 3) :
    ‖ExpStirling.expLocalRemainder θ‖ ≤ Real.exp 3 * |θ| ^ 3 := by
  calc
    ‖ExpStirling.expLocalRemainder θ‖ ≤ |θ| ^ 3 * Real.exp |θ| :=
      ExpStirling.expLocalRemainder_norm_le θ
    _ ≤ |θ| ^ 3 * Real.exp 3 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 3)
    _ = Real.exp 3 * |θ| ^ 3 := by ring

lemma blocks3_local_exponent_norm_le_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ θ : ℝ, |θ| ≤ blocks3SaddleDeltaReal r →
      ‖blocks3LocalExponent r θ‖ ≤ blocks3LocalConstant * blocks3LocalControl r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3_delta_le_one_eventually] with
    r hr hδ_le_one θ hθδ
  let δ : ℝ := blocks3SaddleDeltaReal r
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, blocks3SaddleDeltaReal]
    positivity
  have hθ_one : |θ| ≤ 1 := hθδ.trans hδ_le_one
  have hθ_three : |θ| ≤ 3 := hθ_one.trans (by norm_num)
  have h2θ_three : |2 * θ| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hθ_one]
  have h3θ_three : |3 * θ| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hθ_one]
  have hθ3δ3 : |θ| ^ 3 ≤ δ ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg θ) hθδ 3
  have h2θ3 : |2 * θ| ^ 3 ≤ 8 * δ ^ 3 := by
    calc
      |2 * θ| ^ 3 = 8 * |θ| ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      _ ≤ 8 * δ ^ 3 := mul_le_mul_of_nonneg_left hθ3δ3 (by norm_num)
  have h3θ3 : |3 * θ| ^ 3 ≤ 27 * δ ^ 3 := by
    calc
      |3 * θ| ^ 3 = 27 * |θ| ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        ring_nf
      _ ≤ 27 * δ ^ 3 := mul_le_mul_of_nonneg_left hθ3δ3 (by norm_num)
  have hrem1 := expLocalRemainder_norm_le_exp_three hθ_three
  have hrem2 := expLocalRemainder_norm_le_exp_three h2θ_three
  have hrem3 := expLocalRemainder_norm_le_exp_three h3θ_three
  have hterm1 :
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ ≤
        Real.exp 3 * (r * δ ^ 3) := by
    calc
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖
          = r * ‖ExpStirling.expLocalRemainder θ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (Real.exp 3 * |θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem1 hr0
      _ ≤ r * (Real.exp 3 * δ ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθ3δ3 (Real.exp_pos 3).le) hr0
      _ = Real.exp 3 * (r * δ ^ 3) := by ring_nf
  have hterm2 :
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ ≤
        4 * Real.exp 3 * (r ^ 2 * δ ^ 3) := by
    have hcoef0 : 0 ≤ r ^ 2 / 2 := by positivity
    calc
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖
          = (r ^ 2 / 2) * ‖ExpStirling.expLocalRemainder (2 * θ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
      _ ≤ (r ^ 2 / 2) * (Real.exp 3 * |2 * θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem2 hcoef0
      _ ≤ (r ^ 2 / 2) * (Real.exp 3 * (8 * δ ^ 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2θ3 (Real.exp_pos 3).le) hcoef0
      _ = 4 * Real.exp 3 * (r ^ 2 * δ ^ 3) := by
        have hcoeff : (2 : ℝ)⁻¹ * 8 = 4 := by norm_num
        calc
          (r ^ 2 / 2) * (Real.exp 3 * (8 * δ ^ 3)) =
              ((2 : ℝ)⁻¹ * 8) * (Real.exp 3 * (r ^ 2 * δ ^ 3)) := by
            rw [div_eq_mul_inv]
            ac_rfl
          _ = 4 * Real.exp 3 * (r ^ 2 * δ ^ 3) := by
            rw [hcoeff]
            exact (mul_assoc (4 : ℝ) (Real.exp 3) (r ^ 2 * δ ^ 3)).symm
  have hterm3 :
      ‖(((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))‖ ≤
        (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) := by
    have hcoef0 : 0 ≤ r ^ 3 / 6 := by positivity
    calc
      ‖(((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))‖
          = (r ^ 3 / 6) * ‖ExpStirling.expLocalRemainder (3 * θ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
      _ ≤ (r ^ 3 / 6) * (Real.exp 3 * |3 * θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem3 hcoef0
      _ ≤ (r ^ 3 / 6) * (Real.exp 3 * (27 * δ ^ 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h3θ3 (Real.exp_pos 3).le) hcoef0
      _ = (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) := by ring_nf
  have hterm1' :
      Real.exp 3 * (r * δ ^ 3) ≤ Real.exp 3 * (r ^ 3 * δ ^ 3) := by
    have one_le_r2 : 1 ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    have hr_le_r3 : r ≤ r ^ 3 := by
      calc
        r = r * 1 := by ring
        _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left one_le_r2 hr0
        _ = r ^ 3 := by ring
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr_le_r3 (pow_nonneg hδ0 3)) (Real.exp_pos 3).le
  have hterm2' :
      4 * Real.exp 3 * (r ^ 2 * δ ^ 3) ≤
        4 * Real.exp 3 * (r ^ 3 * δ ^ 3) := by
    have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
      calc
        r ^ 2 = r ^ 2 * 1 := by ring
        _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
        _ = r ^ 3 := by ring
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr2_le_r3 (pow_nonneg hδ0 3))
      (by positivity)
  calc
    ‖blocks3LocalExponent r θ‖
        ≤ ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ +
          ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ +
            ‖(((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))‖ := by
        let A : ℂ := (r : ℂ) * ExpStirling.expLocalRemainder θ
        let B : ℂ := (((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))
        let C : ℂ := (((r ^ 3 / 6 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (3 * θ))
        change ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖
        calc
          ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
          _ ≤ (‖A‖ + ‖B‖) + ‖C‖ :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right (norm_add_le A B) ‖C‖
          _ = ‖A‖ + ‖B‖ + ‖C‖ := by ring
    _ ≤ Real.exp 3 * (r * δ ^ 3) +
          4 * Real.exp 3 * (r ^ 2 * δ ^ 3) +
            (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) :=
        add_le_add (add_le_add hterm1 hterm2) hterm3
    _ ≤ Real.exp 3 * (r ^ 3 * δ ^ 3) +
          4 * Real.exp 3 * (r ^ 3 * δ ^ 3) +
            (9 / 2) * Real.exp 3 * (r ^ 3 * δ ^ 3) :=
        add_le_add (add_le_add hterm1' hterm2') (le_refl _)
    _ ≤ blocks3LocalConstant * blocks3LocalControl r := by
      unfold blocks3LocalConstant blocks3LocalControl
      dsimp [δ]
      have hnonneg : 0 ≤ r ^ 3 * (r ^ (-(7 / 6 : ℝ))) ^ 3 := by
        positivity
      nlinarith [Real.exp_pos 3, hnonneg]

lemma blocks3_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in atTop, ∀ θ : ℝ,
      |θ| ≤ blocks3SaddleDeltaReal r →
        ‖saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in atTop, blocks3LocalConstant * blocks3LocalControl r ≤ ε / 2 :=
    blocks3LocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in atTop, blocks3LocalConstant * blocks3LocalControl r ≤ 1 :=
    blocks3LocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [blocks3_local_exponent_norm_le_eventually, hsmall, hone] with
    r hloc hsmallr honer θ hθ
  rw [blocks3_saddleLocalRatio_eq]
  have hz : ‖blocks3LocalExponent r θ‖ ≤ blocks3LocalConstant * blocks3LocalControl r :=
    hloc θ hθ
  have hz_one : ‖blocks3LocalExponent r θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp (blocks3LocalExponent r θ) - 1‖
        ≤ 2 * ‖blocks3LocalExponent r θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 * (blocks3LocalConstant * blocks3LocalControl r) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

lemma blocks3_saddleGAt_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt blocks3Fun r n θ‖ =
      Real.exp (r * (Real.cos θ - 1) +
        (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
          (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)) := by
  unfold saddleGAt blocks3Fun
  have hphase : ‖Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hden :
      ‖Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2 + (r : ℂ) ^ 3 / 6)‖ =
        Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.add_re, Complex.add_re]
    have hsq : (((r : ℂ) ^ 2 / 2).re = r ^ 2 / 2) := by
      rw [Complex.div_re]
      have hre : ((r : ℂ) ^ 2).re = r ^ 2 := by
        rw [pow_two, Complex.mul_re]
        simp
        ring
      have him : ((r : ℂ) ^ 2).im = 0 := by
        rw [pow_two, Complex.mul_im]
        simp
      rw [hre, him]
      norm_num [Complex.normSq]
      ring
    have hcube : (((r : ℂ) ^ 3 / 6).re = r ^ 3 / 6) := by
      rw [Complex.div_re]
      have hre : ((r : ℂ) ^ 3).re = r ^ 3 := by
        rw [pow_succ, pow_two, Complex.mul_re]
        simp
        ring
      have him : ((r : ℂ) ^ 3).im = 0 := by
        rw [pow_succ, pow_two, Complex.mul_im]
        simp
      rw [hre, him]
      norm_num [Complex.normSq]
      ring
    rw [hsq, hcube]
    simp
  have hnum_re :
      (((r : ℂ) * Complex.exp (θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 / 2 +
            ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 3 / 6).re =
        r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) +
          (r ^ 3 / 6) * Real.cos (3 * θ) := by
    have hsq_div :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 / 2 =
          (((r ^ 2 / 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I)) := by
      have hsq0 :
          ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
            ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
        rw [mul_pow, ← Complex.exp_nat_mul]
        rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
        rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
            ((2 * θ : ℝ) : ℂ) * Complex.I by
          simpa using complex_two_mul_theta_I θ]
      rw [hsq0]
      norm_num [Complex.ofReal_mul]
      ring_nf
    have hcube_div :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3 / 6 =
          (((r ^ 3 / 6 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I)) := by
      have hcube0 :
          ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3 =
            ((r ^ 3 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I) := by
        rw [mul_pow, ← Complex.exp_nat_mul]
        rw [show (r : ℂ) ^ 3 = ((r ^ 3 : ℝ) : ℂ) by norm_num]
        rw [show (((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
            ((3 * θ : ℝ) : ℂ) * Complex.I by
          simpa using complex_three_mul_theta_I θ]
      rw [hcube0]
      norm_num [Complex.ofReal_mul]
      ring_nf
    rw [hsq_div, hcube_div]
    have hre1 :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re = r * Real.cos θ := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    have hre2 :
        ((((r ^ 2 / 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I)).re =
          (r ^ 2 / 2) * Real.cos (2 * θ)) := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    have hre3 :
        ((((r ^ 3 / 6 : ℝ) : ℂ) * Complex.exp ((3 * θ : ℝ) * Complex.I)).re =
          (r ^ 3 / 6) * Real.cos (3 * θ)) := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.add_re, Complex.add_re, hre1, hre2, hre3]
  have hnum :
      ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2 +
            ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 3 / 6)‖ =
        Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) +
          (r ^ 3 / 6) * Real.cos (3 * θ)) := by
    rw [Complex.norm_exp, hnum_re]
  have hden_pos : 0 < Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) := Real.exp_pos _
  calc
    ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2 +
            ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 3 / 6) /
        Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2 + (r : ℂ) ^ 3 / 6) *
        Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖
        = Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) +
              (r ^ 3 / 6) * Real.cos (3 * θ)) /
            Real.exp (r + r ^ 2 / 2 + r ^ 3 / 6) := by
          rw [norm_mul, hphase, mul_one, norm_div, hnum, hden]
    _ = Real.exp (r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)) := by
      rw [← Real.exp_sub]
      congr 1
      ring_nf

def blocks3TailE (r : ℝ) : ℝ :=
  Real.exp (-(1 / (2 * Real.pi ^ 2)) * r ^ (2 / 3 : ℝ))

lemma blocks3TailE_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ blocks3TailE r :=
  Eventually.of_forall fun r => by
    unfold blocks3TailE
    positivity

lemma blocks3TailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r)
      atTop (𝓝 0) := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (9 / 4 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (9 / 4 : ℝ) c hc
  have hy : Tendsto (fun r : ℝ => r ^ (2 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)
  have hcomp :
      Tendsto (fun r : ℝ => (r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) *
        Real.exp (-c * r ^ (2 / 3 : ℝ))) atTop (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto (fun r : ℝ => Real.sqrt (10 * Real.pi) *
        ((r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) *
          Real.exp (-c * r ^ (2 / 3 : ℝ)))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (10 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · exact Eventually.of_forall fun r => by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have one_le_r2 : 1 ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    have hr_le_r3 : r ≤ r ^ 3 := by
      calc
        r = r * 1 := by ring
        _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left one_le_r2 hr0
        _ = r ^ 3 := by ring
    have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
      calc
        r ^ 2 = r ^ 2 * 1 := by ring
        _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
        _ = r ^ 3 := by ring
    have hB_le : blocks3SaddleBReal r ≤ 5 * r ^ 3 := by
      unfold blocks3SaddleBReal
      nlinarith
    have hsqrt :
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) ≤
          Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
      have hmul : 2 * Real.pi * blocks3SaddleBReal r ≤ 10 * Real.pi * r ^ 3 := by
        calc
          2 * Real.pi * blocks3SaddleBReal r
              ≤ 2 * Real.pi * (5 * r ^ 3) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 10 * Real.pi * r ^ 3 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r)
            ≤ Real.sqrt (10 * Real.pi * r ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
          have h10pi : 0 ≤ 10 * Real.pi := by positivity
          rw [Real.sqrt_mul h10pi (r ^ 3)]
          rw [Real.sqrt_eq_rpow (r ^ 3)]
          have hpow : (r ^ 3) ^ (1 / 2 : ℝ) = r ^ (3 / 2 : ℝ) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hr0]
            norm_num
          rw [hpow]
    have hrpow : (r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) = r ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_mul hr0]
      norm_num
    calc
      Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r
          ≤ (Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ)) * blocks3TailE r :=
            mul_le_mul_of_nonneg_right hsqrt (by
              unfold blocks3TailE
              positivity)
      _ = Real.sqrt (10 * Real.pi) *
            ((r ^ (2 / 3 : ℝ)) ^ (9 / 4 : ℝ) *
              Real.exp (-c * r ^ (2 / 3 : ℝ))) := by
        unfold blocks3TailE
        dsimp [c]
        rw [hrpow]
        ring_nf

lemma blocks3_tail_bound_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
      blocks3SaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt blocks3Fun r n θ‖ ≤ blocks3TailE r := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hc_le_three : c ≤ 3 / Real.pi ^ 2 := by
    dsimp [c]
    field_simp [Real.pi_ne_zero]
    norm_num
  have hc_le_two_ninths : c ≤ 2 / 9 := by
    dsimp [c]
    have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.two_le_pi]
    have hden : 0 < 2 * Real.pi ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr n θ hδθ hθπ
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ blocks3SaddleDeltaReal r := by
    unfold blocks3SaddleDeltaReal
    positivity
  rw [blocks3_saddleGAt_norm]
  unfold blocks3TailE
  apply Real.exp_le_exp.mpr
  by_cases hsmall : |θ| ≤ Real.pi / 3
  · have h3θπ : |3 * θ| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      nlinarith
    have hcos3 := Real.cos_le_one_sub_mul_cos_sq h3θπ
    have hcos3_sub : Real.cos (3 * θ) - 1 ≤
        -(2 / Real.pi ^ 2) * (3 * θ) ^ 2 := by
      linarith
    have htail_scale :
        r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2 = r ^ (2 / 3 : ℝ) := by
      have hr3_rpow : r ^ 3 = r ^ (3 : ℝ) := by
        exact (Real.rpow_natCast r 3).symm
      have hdelta_pow :
          (r ^ (-(7 / 6 : ℝ))) ^ 2 = r ^ (-(7 / 6 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hr0 (-(7 / 6 : ℝ)) 2).symm
      unfold blocks3SaddleDeltaReal
      calc
        r ^ 3 * (r ^ (-(7 / 6 : ℝ))) ^ 2
            = r ^ (3 : ℝ) * r ^ (-(7 / 6 : ℝ) * (2 : ℝ)) := by
              rw [hr3_rpow, hdelta_pow]
        _ = r ^ ((3 : ℝ) + (-(7 / 6 : ℝ) * (2 : ℝ))) := by
              rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hr)]
        _ = r ^ (2 / 3 : ℝ) := by norm_num
    have hθsq : (blocks3SaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
      calc
        (blocks3SaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ hδ0 hδθ 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hmain :
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
          ≤ -c * r ^ (2 / 3 : ℝ) := by
      have hcos1_nonpos : Real.cos θ - 1 ≤ 0 := by
        linarith [Real.cos_le_one θ]
      have hcos2_nonpos : Real.cos (2 * θ) - 1 ≤ 0 := by
        linarith [Real.cos_le_one (2 * θ)]
      have hleft_nonpos : r * (Real.cos θ - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hr0 hcos1_nonpos
      have hmiddle_nonpos : (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos2_nonpos
      have hcoef_nonpos : -(3 / Real.pi ^ 2) ≤ 0 := by
        have hpos : 0 ≤ 3 / Real.pi ^ 2 := by positivity
        linarith
      have hstrong :
          (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
            ≤ -(3 / Real.pi ^ 2) * (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2) := by
        calc
          (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
              ≤ (r ^ 3 / 6) * (-(2 / Real.pi ^ 2) * (3 * θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hcos3_sub (by positivity)
          _ = -(3 / Real.pi ^ 2) * (r ^ 3 * θ ^ 2) := by ring_nf
          _ ≤ -(3 / Real.pi ^ 2) *
                (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2) := by
            exact mul_le_mul_of_nonpos_left
              (mul_le_mul_of_nonneg_left hθsq (by positivity)) hcoef_nonpos
      have hconst : c * r ^ (2 / 3 : ℝ) ≤
          (3 / Real.pi ^ 2) * (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2) := by
        rw [htail_scale]
        exact mul_le_mul_of_nonneg_right hc_le_three (Real.rpow_nonneg hr0 _)
      calc
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
            ≤ 0 + 0 +
                (-(3 / Real.pi ^ 2) *
                  (r ^ 3 * (blocks3SaddleDeltaReal r) ^ 2)) :=
              add_le_add (add_le_add hleft_nonpos hmiddle_nonpos) hstrong
        _ ≤ -c * r ^ (2 / 3 : ℝ) := by linarith
    exact hmain
  · have hlarge : Real.pi / 3 < |θ| := lt_of_not_ge hsmall
    have hcos1 := Real.cos_le_one_sub_mul_cos_sq hθπ
    have hcos1_sub : Real.cos θ - 1 ≤ -(2 / Real.pi ^ 2) * θ ^ 2 := by
      linarith
    have hθsq_lower : (Real.pi / 3) ^ 2 ≤ θ ^ 2 := by
      calc
        (Real.pi / 3) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlarge.le 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hmain :
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
          ≤ -c * r ^ (2 / 3 : ℝ) := by
      have hcos2_nonpos : Real.cos (2 * θ) - 1 ≤ 0 := by
        linarith [Real.cos_le_one (2 * θ)]
      have hcos3_nonpos : Real.cos (3 * θ) - 1 ≤ 0 := by
        linarith [Real.cos_le_one (3 * θ)]
      have hmiddle_nonpos : (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos2_nonpos
      have hright_nonpos : (r ^ 3 / 6) * (Real.cos (3 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos3_nonpos
      have hcoef_nonpos : -(2 / Real.pi ^ 2) ≤ 0 := by
        have hpos : 0 ≤ 2 / Real.pi ^ 2 := by positivity
        linarith
      have hfirst :
          r * (Real.cos θ - 1) ≤ -(2 / 9) * r := by
        calc
          r * (Real.cos θ - 1)
              ≤ r * (-(2 / Real.pi ^ 2) * θ ^ 2) :=
                mul_le_mul_of_nonneg_left hcos1_sub hr0
          _ ≤ r * (-(2 / Real.pi ^ 2) * (Real.pi / 3) ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonpos_left hθsq_lower hcoef_nonpos) hr0
          _ = -(2 / 9) * r := by
            field_simp [Real.pi_ne_zero]
            ring
      have hpow_le : r ^ (2 / 3 : ℝ) ≤ r := by
        calc
          r ^ (2 / 3 : ℝ) ≤ r ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (2 / 3 : ℝ) ≤ 1)
          _ = r := by rw [Real.rpow_one]
      have hconst : c * r ^ (2 / 3 : ℝ) ≤ (2 / 9) * r := by
        calc
          c * r ^ (2 / 3 : ℝ) ≤ (2 / 9) * r ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right hc_le_two_ninths (Real.rpow_nonneg hr0 _)
          _ ≤ (2 / 9) * r :=
            mul_le_mul_of_nonneg_left hpow_le (by norm_num)
      calc
        r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) +
            (r ^ 3 / 6) * (Real.cos (3 * θ) - 1)
            ≤ -(2 / 9) * r + 0 + 0 :=
              add_le_add (add_le_add hfirst hmiddle_nonpos) hright_nonpos
        _ ≤ -c * r ^ (2 / 3 : ℝ) := by linarith
    exact hmain

lemma blocks3_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in atTop, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * E r)
        atTop (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        blocks3SaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt blocks3Fun r n θ‖ ≤ E r) := by
  exact ⟨blocks3TailE, blocks3TailE_nonneg_eventually, blocks3TailE_decay,
    blocks3_tail_bound_eventually⟩

lemma blocks3SaddleAReal_strictMonoOn_nonneg :
    StrictMonoOn blocks3SaddleAReal (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold blocks3SaddleAReal
  have hdiff : 0 < y - x := sub_pos.mpr hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hquad_nonneg : 0 ≤ (x ^ 2 + x * y + y ^ 2) / 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, hxy0]
  have hfactor : 0 < 1 + x + y + (x ^ 2 + x * y + y ^ 2) / 2 := by
    linarith
  have hpos : 0 < (y - x) *
      (1 + x + y + (x ^ 2 + x * y + y ^ 2) / 2) :=
    mul_pos hdiff hfactor
  nlinarith

lemma blocks3SaddleRadius_nonneg (n : ℕ) : 0 ≤ blocks3SaddleRadius n :=
  (Classical.choose_spec
    (blocks3SaddleAReal_exists_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))).1

lemma blocks3SaddleAReal_radius (n : ℕ) :
    blocks3SaddleAReal (blocks3SaddleRadius n) = (n : ℝ) :=
  (Classical.choose_spec
    (blocks3SaddleAReal_exists_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))).2

lemma blocks3SaddleRadius_tendsto_atTop :
    Tendsto blocks3SaddleRadius atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  let M0 : ℝ := max M 0
  obtain ⟨N, hN⟩ := exists_nat_gt (blocks3SaddleAReal M0)
  refine ⟨N, fun n hn => ?_⟩
  have hM0_nonneg : 0 ≤ M0 := le_max_right _ _
  have hM_le_M0 : M ≤ M0 := le_max_left _ _
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAM0_lt_n : blocks3SaddleAReal M0 < (n : ℝ) := hN.trans_le hnR
  by_contra hnot
  have hr_lt_M : blocks3SaddleRadius n < M := lt_of_not_ge hnot
  have hr_lt_M0 : blocks3SaddleRadius n < M0 := hr_lt_M.trans_le hM_le_M0
  have hstrict :
      blocks3SaddleAReal (blocks3SaddleRadius n) < blocks3SaddleAReal M0 :=
    blocks3SaddleAReal_strictMonoOn_nonneg
      (blocks3SaddleRadius_nonneg n) hM0_nonneg hr_lt_M0
  rw [blocks3SaddleAReal_radius] at hstrict
  linarith

def blocks3HAdmissible : HAdmissible blocks3Fun blocks3Series where
  ρ := blocks3Series.radius
  radFilter := atTop
  a := blocks3SaddleAReal
  b := blocks3SaddleBReal
  δ := blocks3SaddleDeltaReal
  hp := blocks3Fun_hasFPowerSeriesAt_zero
  radius_eq := rfl
  radius_pos := by
    simpa [blocks3Series] using blocks3Fun_hasFPowerSeriesAt_zero.radius_pos
  rad_neBot := by infer_instance
  r_pos := eventually_gt_atTop (0 : ℝ)
  differentiableOn := blocks3_differentiableOn_eventually
  f_pos := blocks3_f_pos_eventually
  b_pos := blocks3_b_pos_eventually
  δ_pos := blocks3_delta_pos_eventually
  δ_le_pi := blocks3_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := blocks3_delta_sqrt_b_tendsto_atTop
  local_uniform := blocks3_local_uniform
  tail_uniform := blocks3_tail_uniform

def blocks3HAdmissibleSaddleSequence : SaddleSequence blocks3HAdmissible where
  r := blocks3SaddleRadius
  tendsTo := by
    simpa [blocks3HAdmissible] using blocks3SaddleRadius_tendsto_atTop
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change blocks3SaddleAReal (blocks3SaddleRadius n) = (n : ℝ)
      exact blocks3SaddleAReal_radius n

end Blocks3HAdmissible
end
end

section
/-!
# Second-order saddle data for blocks of size at most three

This file adds the second-order correction layer for
`exp (z + z^2 / 2 + z^3 / 6)`.  The logarithmic saddle derivatives are
`b₃(r)=r+4r²+9r³/2` and `b₄(r)=r+8r²+27r³/2`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

namespace Blocks3HAdmissible

lemma blocks3SecondCorrScale_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < blocks3SecondCorrScale r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold blocks3SecondCorrScale
  exact Real.rpow_pos_of_pos hr _

lemma blocks3SecondCorrScale_tendsto_zero :
    Tendsto blocks3SecondCorrScale atTop (𝓝 0) := by
  change Tendsto (fun r : ℝ => r ^ (-(3 : ℝ))) atTop (𝓝 0)
  exact tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)

lemma blocks3_saddleCorrectionScale_le_secondCorrScale_eventually :
    ∀ᶠ r : ℝ in atTop,
      saddleCorrectionScale blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r ≤
        1000000 * blocks3SecondCorrScale r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < blocks3SaddleBReal r := by
    unfold blocks3SaddleBReal
    positivity
  have hb4_nonneg : 0 ≤ blocks3SaddleB4Real r := by
    unfold blocks3SaddleB4Real
    positivity
  unfold saddleCorrectionScale blocks3SaddleBReal blocks3SaddleB3Real
    blocks3SaddleB4Real blocks3SecondCorrScale
  rw [abs_of_nonneg (by simpa [blocks3SaddleB4Real] using hb4_nonneg)]
  rw [Real.rpow_neg hrpos.le]
  field_simp [hrpos.ne', hbpos.ne']
  ring_nf
  have h1_le_r2 : (1 : ℝ) ≤ r ^ 2 := by
    nlinarith [sq_nonneg (r - 1)]
  have h1_le_r3 : (1 : ℝ) ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr h1_le_r2 zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have h1_le_r4 : (1 : ℝ) ≤ r ^ 4 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r ^ 2 * r ^ 2 :=
        mul_le_mul h1_le_r2 h1_le_r2 zero_le_one (sq_nonneg r)
      _ = r ^ 4 := by ring
  have hr3_le_r7 : r ^ 3 ≤ r ^ 7 := by
    calc
      r ^ 3 = r ^ 3 * 1 := by ring
      _ ≤ r ^ 3 * r ^ 4 :=
        mul_le_mul_of_nonneg_left h1_le_r4 (by positivity)
      _ = r ^ 7 := by ring
  have hr4_le_r7 : r ^ 4 ≤ r ^ 7 := by
    calc
      r ^ 4 = r ^ 4 * 1 := by ring
      _ ≤ r ^ 4 * r ^ 3 :=
        mul_le_mul_of_nonneg_left h1_le_r3 (by positivity)
      _ = r ^ 7 := by ring
  have hr5_le_r7 : r ^ 5 ≤ r ^ 7 := by
    calc
      r ^ 5 = r ^ 5 * 1 := by ring
      _ ≤ r ^ 5 * r ^ 2 :=
        mul_le_mul_of_nonneg_left h1_le_r2 (by positivity)
      _ = r ^ 7 := by ring
  have hr6_le_r7 : r ^ 6 ≤ r ^ 7 := by
    calc
      r ^ 6 = r ^ 6 * 1 := by ring
      _ ≤ r ^ 6 * r := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = r ^ 7 := by ring
  calc
    r * r ^ (3 : ℝ) * 144 + r ^ 2 * r ^ (3 : ℝ) * 448 +
          r ^ 3 * r ^ (3 : ℝ) * 600 + r ^ 4 * r ^ (3 : ℝ) * 324 +
            r ^ (3 : ℝ) * 16
        = 144 * r ^ 4 + 448 * r ^ 5 + 600 * r ^ 6 + 324 * r ^ 7 +
            16 * r ^ 3 := by
          rw [show r ^ (3 : ℝ) = r ^ 3 by
            exact Real.rpow_natCast r 3]
          ring
    _ ≤ 144 * r ^ 7 + 448 * r ^ 7 + 600 * r ^ 7 + 324 * r ^ 7 +
          16 * r ^ 7 := by
        gcongr
    _ ≤ r * 8000000 + r ^ 2 * 48000000 + r ^ 3 * 132000000 +
          r ^ 4 * 208000000 + r ^ 5 * 198000000 + r ^ 6 * 108000000 +
            r ^ 7 * 27000000 := by
        nlinarith [show 0 ≤ r by positivity, show 0 ≤ r ^ 2 by positivity,
          show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
          show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
          show 0 ≤ r ^ 7 by positivity]

lemma blocks3_tail_second_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r /
          blocks3SecondCorrScale r)
      atTop (𝓝 0) := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (27 / 4 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (27 / 4 : ℝ) c hc
  have hy : Tendsto (fun r : ℝ => r ^ (2 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)
  have hcomp :
      Tendsto (fun r : ℝ => (r ^ (2 / 3 : ℝ)) ^ (27 / 4 : ℝ) *
        Real.exp (-c * r ^ (2 / 3 : ℝ))) atTop (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto (fun r : ℝ => Real.sqrt (10 * Real.pi) *
        ((r ^ (2 / 3 : ℝ)) ^ (27 / 4 : ℝ) *
          Real.exp (-c * r ^ (2 / 3 : ℝ)))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (10 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · filter_upwards [blocks3SecondCorrScale_pos_eventually] with r hcorr
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by unfold blocks3TailE; positivity)) hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hcorr_pos : 0 < blocks3SecondCorrScale r := by
      unfold blocks3SecondCorrScale
      exact Real.rpow_pos_of_pos hrpos _
    have one_le_r2 : 1 ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    have hr_le_r3 : r ≤ r ^ 3 := by
      calc
        r = r * 1 := by ring
        _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left one_le_r2 hr0
        _ = r ^ 3 := by ring
    have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
      calc
        r ^ 2 = r ^ 2 * 1 := by ring
        _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
        _ = r ^ 3 := by ring
    have hB_le : blocks3SaddleBReal r ≤ 5 * r ^ 3 := by
      unfold blocks3SaddleBReal
      nlinarith
    have hsqrt :
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) ≤
          Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
      have hmul : 2 * Real.pi * blocks3SaddleBReal r ≤ 10 * Real.pi * r ^ 3 := by
        calc
          2 * Real.pi * blocks3SaddleBReal r
              ≤ 2 * Real.pi * (5 * r ^ 3) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 10 * Real.pi * r ^ 3 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r)
            ≤ Real.sqrt (10 * Real.pi * r ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ) := by
          have h10pi : 0 ≤ 10 * Real.pi := by positivity
          rw [Real.sqrt_mul h10pi (r ^ 3)]
          rw [Real.sqrt_eq_rpow (r ^ 3)]
          have hpow : (r ^ 3) ^ (1 / 2 : ℝ) = r ^ (3 / 2 : ℝ) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hr0]
            norm_num
          rw [hpow]
    have hE_nonneg : 0 ≤ blocks3TailE r := by
      unfold blocks3TailE
      positivity
    have hnum :
        Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r ≤
          (Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ)) * blocks3TailE r :=
      mul_le_mul_of_nonneg_right hsqrt hE_nonneg
    have hrpow :
        (r ^ (2 / 3 : ℝ)) ^ (27 / 4 : ℝ) = r ^ (9 / 2 : ℝ) := by
      rw [← Real.rpow_mul hr0]
      norm_num
    calc
      Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * blocks3TailE r /
          blocks3SecondCorrScale r
          ≤ (Real.sqrt (10 * Real.pi) * r ^ (3 / 2 : ℝ)) * blocks3TailE r /
              blocks3SecondCorrScale r :=
            div_le_div_of_nonneg_right hnum hcorr_pos.le
      _ = Real.sqrt (10 * Real.pi) *
            ((r ^ (2 / 3 : ℝ)) ^ (27 / 4 : ℝ) *
              Real.exp (-c * r ^ (2 / 3 : ℝ))) := by
        unfold blocks3TailE blocks3SecondCorrScale
        dsimp [c]
        rw [Real.rpow_neg hr0]
        rw [hrpow]
        field_simp [hrpos.ne']
        rw [← Real.rpow_add hrpos]
        norm_num

lemma blocks3_tail_second_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in atTop, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * blocks3SaddleBReal r) * E r /
          blocks3SecondCorrScale r)
        atTop (𝓝 0) ∧
      (∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        blocks3SaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt blocks3Fun r n θ‖ ≤ E r) := by
  exact ⟨blocks3TailE, blocks3TailE_nonneg_eventually, blocks3_tail_second_decay,
    blocks3_tail_bound_eventually⟩

private def expLocalRemainderFifth (θ : ℝ) : ℂ :=
  ExpStirling.expLocalRemainder θ -
    ((((θ : ℂ) * Complex.I) ^ 3) / (((3 : ℕ).factorial : ℕ) : ℂ) +
      (((θ : ℂ) * Complex.I) ^ 4) / (((4 : ℕ).factorial : ℕ) : ℂ))

private lemma expLocalRemainderFifth_norm_le {θ : ℝ} (hθ : |θ| ≤ 3) :
    ‖expLocalRemainderFifth θ‖ ≤ Real.exp 3 * |θ| ^ 5 := by
  let u : ℂ := (θ : ℂ) * Complex.I
  have htail := Complex.norm_exp_sub_sum_le_norm_mul_exp u 5
  have hnorm : ‖u‖ = |θ| := by simp [u]
  have hleft :
      ExpStirling.expLocalRemainder θ -
          (u ^ 3 / (((3 : ℕ).factorial : ℕ) : ℂ) +
            u ^ 4 / (((4 : ℕ).factorial : ℕ) : ℂ)) =
        Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ) := by
    simp [ExpStirling.expLocalRemainder, u, Finset.sum_range_succ]
    ring
  change
    ‖ExpStirling.expLocalRemainder θ -
        (u ^ 3 / (((3 : ℕ).factorial : ℕ) : ℂ) +
          u ^ 4 / (((4 : ℕ).factorial : ℕ) : ℂ))‖ ≤
      Real.exp 3 * |θ| ^ 5
  rw [hleft]
  calc
    ‖Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ)‖
        ≤ ‖u‖ ^ 5 * Real.exp ‖u‖ := htail
    _ = |θ| ^ 5 * Real.exp |θ| := by rw [hnorm]
    _ ≤ |θ| ^ 5 * Real.exp 3 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 5)
    _ = Real.exp 3 * |θ| ^ 5 := by ring

private lemma blocks3LocalExponent_split_fifth (r θ : ℝ) :
    blocks3LocalExponent r θ =
      -Complex.I * ((blocks3SaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
        ((blocks3SaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
        (r : ℂ) * expLocalRemainderFifth θ +
        (((r ^ 2 / 2 : ℝ) : ℂ) * expLocalRemainderFifth (2 * θ)) +
          (((r ^ 3 / 6 : ℝ) : ℂ) * expLocalRemainderFifth (3 * θ)) := by
  unfold blocks3LocalExponent expLocalRemainderFifth blocks3SaddleB3Real blocks3SaddleB4Real
  ring_nf
  simp [Complex.I_pow_three, Complex.I_pow_four]
  ring_nf

private def blocks3ScaledCubic (r x : ℝ) : ℂ :=
  -Complex.I *
    ((blocks3SaddleB3Real r : ℂ) /
      (6 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3)) * (x : ℂ) ^ 3

private def blocks3ScaledQuartic (r x : ℝ) : ℂ :=
  ((blocks3SaddleB4Real r : ℂ) /
      (24 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4)) *
    (x : ℂ) ^ 4

private def blocks3ScaledRemainder (r x : ℝ) : ℂ :=
  (r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r)) +
    (((r ^ 2 / 2 : ℝ) : ℂ) *
      expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r)))) +
      (((r ^ 3 / 6 : ℝ) : ℂ) *
        expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))

private lemma blocks3SaddleBReal_pos_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 < blocks3SaddleBReal r := by
  unfold blocks3SaddleBReal
  positivity

private lemma blocks3_sqrtB_sq {r : ℝ} (hb : 0 < blocks3SaddleBReal r) :
    ((Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 2) =
      (blocks3SaddleBReal r : ℂ) := by
  exact_mod_cast (Real.sq_sqrt hb.le)

private lemma blocks3_sqrtB_ge_rpow_three_halves {r : ℝ} (hr : 1 ≤ r) :
    r ^ (3 / 2 : ℝ) ≤ Real.sqrt (blocks3SaddleBReal r) := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hb_ge : r ^ 3 ≤ blocks3SaddleBReal r := by
    unfold blocks3SaddleBReal
    nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) hr0]
  have hrpow_sq : (r ^ (3 / 2 : ℝ)) ^ 2 = r ^ 3 := by
    calc
      (r ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = r ^ ((3 / 2 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hr0 (3 / 2 : ℝ) 2).symm
      _ = r ^ (3 : ℝ) :=
        congrArg (fun e : ℝ => r ^ e) (by norm_num : (3 / 2 : ℝ) * 2 = 3)
      _ = r ^ (3 : ℕ) := Real.rpow_natCast r 3
  exact Real.le_sqrt_of_sq_le (by simpa [hrpow_sq] using hb_ge)

private lemma blocks3LocalExponent_scaled_split {r x : ℝ}
    (hb : 0 < blocks3SaddleBReal r) :
    blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r)) =
      blocks3ScaledCubic r x + blocks3ScaledQuartic r x + blocks3ScaledRemainder r x := by
  have hsqrt_ne : (Real.sqrt (blocks3SaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hsqrt_sq := blocks3_sqrtB_sq hb
  rw [blocks3LocalExponent_split_fifth]
  unfold blocks3ScaledCubic blocks3ScaledQuartic blocks3ScaledRemainder
  simp [Complex.ofReal_inv, div_eq_mul_inv]
  field_simp [hsqrt_ne]
  ring_nf

private lemma blocks3_saddleSecondPoly_eq_scaled_terms {r x : ℝ}
    (hb : 0 < blocks3SaddleBReal r) :
    saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x =
      1 + blocks3ScaledCubic r x + blocks3ScaledQuartic r x +
        (blocks3ScaledCubic r x) ^ 2 / 2 := by
  have hsqrt_sq := blocks3_sqrtB_sq hb
  have hsqrt_ne : (Real.sqrt (blocks3SaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (blocks3SaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_pow6 :
      (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 6 =
        (blocks3SaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (blocks3SaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
  have hsqrt_pow4 :
      (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4 =
        (blocks3SaddleBReal r : ℂ) ^ 2 := by
    calc
      (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4 =
          ((Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 2) ^ 2 := by ring
      _ = (blocks3SaddleBReal r : ℂ) ^ 2 := by rw [hsqrt_sq]
  unfold saddleSecondPoly blocks3ScaledCubic blocks3ScaledQuartic
  field_simp [hsqrt_ne, hb_ne]
  ring_nf
  rw [hsqrt_pow6, hsqrt_sq, Complex.I_sq]
  norm_num [Complex.ofReal_pow]
  ring

private lemma blocks3ScaledCubic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖blocks3ScaledCubic r x‖ ≤ 10 * r ^ (-(3 / 2 : ℝ)) * |x| ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ^ (3 / 2 : ℝ) ≤ Real.sqrt (blocks3SaddleBReal r) :=
    blocks3_sqrtB_ge_rpow_three_halves hr
  have hsqrt3_ge :
      (r ^ (3 / 2 : ℝ)) ^ 3 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 3 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ (3 / 2 : ℝ)) hsqrt_ge 3
  have hb3_nonneg : 0 ≤ blocks3SaddleB3Real r := by
    unfold blocks3SaddleB3Real
    positivity
  have hb3_le : blocks3SaddleB3Real r ≤ 10 * r ^ 3 := by
    unfold blocks3SaddleB3Real
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]
  have hrpow3 :
      (r ^ (3 / 2 : ℝ)) ^ 3 = r ^ ((3 / 2 : ℝ) * 3) :=
    (Real.rpow_mul_natCast hr0 (3 / 2 : ℝ) 3).symm
  have hcoef :
      ‖(blocks3SaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3)‖ ≤
        10 * r ^ (-(3 / 2 : ℝ)) := by
    calc
      ‖(blocks3SaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3)‖
          = blocks3SaddleB3Real r /
              (6 * (Real.sqrt (blocks3SaddleBReal r)) ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb3_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hsqrt_pos]
      _ ≤ (10 * r ^ 3) / (6 * (r ^ (3 / 2 : ℝ)) ^ 3) := by
            exact div_le_div₀ (by positivity) hb3_le (by positivity)
              (by nlinarith [hsqrt3_ge])
      _ ≤ 10 * r ^ (-(3 / 2 : ℝ)) := by
            rw [hrpow3]
            rw [show (3 / 2 : ℝ) * 3 = 3 + 3 / 2 by norm_num]
            rw [Real.rpow_add hrpos]
            rw [Real.rpow_neg hr0]
            have ha : 0 < r ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hrpos _
            have hnat3 : r ^ 3 = r ^ (3 : ℝ) := by
              exact (Real.rpow_natCast r 3).symm
            rw [← hnat3]
            have hden : 0 < 6 * (r ^ 3 * r ^ (3 / 2 : ℝ)) := by positivity
            rw [div_le_iff₀ hden]
            field_simp [ha.ne']
            nlinarith [show 0 ≤ r ^ 3 by positivity]
  calc
    ‖blocks3ScaledCubic r x‖
        = ‖(blocks3SaddleB3Real r : ℂ) /
            (6 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3)‖ * |x| ^ 3 := by
          unfold blocks3ScaledCubic
          rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * r ^ (-(3 / 2 : ℝ))) * |x| ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 3)
    _ = 10 * r ^ (-(3 / 2 : ℝ)) * |x| ^ 3 := by ring

private lemma blocks3ScaledQuartic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖blocks3ScaledQuartic r x‖ ≤ 10 * r ^ (-(3 : ℝ)) * |x| ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hb_ge : r ^ 3 ≤ blocks3SaddleBReal r := by
    unfold blocks3SaddleBReal
    nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) hr0]
  have hb_sq_ge : (r ^ 3) ^ 2 ≤ (blocks3SaddleBReal r) ^ 2 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 3) hb_ge 2
  have hb4_nonneg : 0 ≤ blocks3SaddleB4Real r := by
    unfold blocks3SaddleB4Real
    positivity
  have hb4_le : blocks3SaddleB4Real r ≤ 30 * r ^ 3 := by
    unfold blocks3SaddleB4Real
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]
  have hcoef :
      ‖(blocks3SaddleB4Real r : ℂ) /
          (24 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4)‖ ≤
        10 * r ^ (-(3 : ℝ)) := by
    calc
      ‖(blocks3SaddleB4Real r : ℂ) /
          (24 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4)‖
          = blocks3SaddleB4Real r / (24 * (Real.sqrt (blocks3SaddleBReal r)) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb4_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos (Real.sqrt_pos.mpr hbpos)]
      _ ≤ (30 * r ^ 3) / (24 * (r ^ (3 / 2 : ℝ)) ^ 4) := by
            have hsqrt4_ge :
                (r ^ (3 / 2 : ℝ)) ^ 4 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 4 :=
              pow_le_pow_left₀ (by positivity : 0 ≤ r ^ (3 / 2 : ℝ))
                (blocks3_sqrtB_ge_rpow_three_halves hr) 4
            exact div_le_div₀ (by positivity) hb4_le (by positivity)
              (by nlinarith [hsqrt4_ge])
      _ ≤ 10 * r ^ (-(3 : ℝ)) := by
            have hrpow4 :
                (r ^ (3 / 2 : ℝ)) ^ 4 = r ^ ((3 / 2 : ℝ) * 4) :=
              (Real.rpow_mul_natCast hr0 (3 / 2 : ℝ) 4).symm
            rw [hrpow4]
            rw [show (3 / 2 : ℝ) * 4 = 6 by norm_num]
            have hneg3 : r ^ (-(3 : ℝ)) = (r ^ 3)⁻¹ := by
              calc
                r ^ (-(3 : ℝ)) = (r ^ (3 : ℝ))⁻¹ := Real.rpow_neg hr0 (3 : ℝ)
                _ = (r ^ 3)⁻¹ := congrArg (fun t : ℝ => t⁻¹) (Real.rpow_natCast r 3)
            rw [hneg3]
            rw [show r ^ (6 : ℝ) = r ^ 6 by exact Real.rpow_natCast r 6]
            have hden : 0 < 24 * r ^ 6 := by positivity
            rw [div_le_iff₀ hden]
            field_simp [hrpos.ne']
            nlinarith [show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 6 by positivity]
  calc
    ‖blocks3ScaledQuartic r x‖
        = ‖(blocks3SaddleB4Real r : ℂ) /
            (24 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 4)‖ * |x| ^ 4 := by
          unfold blocks3ScaledQuartic
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * r ^ (-(3 : ℝ))) * |x| ^ 4 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 4)
    _ = 10 * r ^ (-(3 : ℝ)) * |x| ^ 4 := by ring

private def blocks3LocalTaylorConst : ℝ :=
  10000 * Real.exp 3

private lemma blocks3LocalTaylorConst_pos : 0 < blocks3LocalTaylorConst := by
  unfold blocks3LocalTaylorConst
  positivity

private lemma blocks3ScaledRemainder_norm_le {r x : ℝ}
    (hr : 1 ≤ r) (hθ : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ 1) :
    ‖blocks3ScaledRemainder r x‖ ≤
      blocks3LocalTaylorConst * r ^ (-(9 / 2 : ℝ)) * |x| ^ 5 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ^ (3 / 2 : ℝ) ≤ Real.sqrt (blocks3SaddleBReal r) :=
    blocks3_sqrtB_ge_rpow_three_halves hr
  let A : ℝ := r ^ (-(3 / 2 : ℝ))
  let D : ℝ := r ^ (-(9 / 2 : ℝ))
  let y : ℝ := |x|
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact abs_nonneg x
  have hA5D : r ^ 3 * A ^ 5 = D := by
    dsimp [A, D]
    rw [(Real.rpow_mul_natCast hr0 (-(3 / 2 : ℝ)) 5).symm]
    rw [show r ^ 3 = r ^ (3 : ℝ) by exact (Real.rpow_natCast r 3).symm]
    rw [← Real.rpow_add hrpos]
    norm_num
  have hA5_nonneg : 0 ≤ A ^ 5 := pow_nonneg hA_nonneg 5
  have hr_le_r3 : r ≤ r ^ 3 := by
    have h1_le_r2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
    calc
      r = r * 1 := by ring
      _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left h1_le_r2 hr0
      _ = r ^ 3 := by ring
  have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by
    calc
      r ^ 2 = r ^ 2 * 1 := by ring
      _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
      _ = r ^ 3 := by ring
  have hrA5_le_D : r * A ^ 5 ≤ D := by
    calc
      r * A ^ 5 ≤ r ^ 3 * A ^ 5 :=
        mul_le_mul_of_nonneg_right hr_le_r3 hA5_nonneg
      _ = D := hA5D
  have hr2A5_le_D : r ^ 2 * A ^ 5 ≤ D := by
    calc
      r ^ 2 * A ^ 5 ≤ r ^ 3 * A ^ 5 :=
        mul_le_mul_of_nonneg_right hr2_le_r3 hA5_nonneg
      _ = D := hA5D
  have hr3A5_le_D : r ^ 3 * A ^ 5 ≤ D := by rw [hA5D]
  have hθ_abs_le : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ A * y := by
    rw [abs_div, abs_of_pos hsqrt_pos]
    have hbase :
        |x| / Real.sqrt (blocks3SaddleBReal r) ≤ |x| / r ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (abs_nonneg x)
        (Real.rpow_pos_of_pos hrpos (3 / 2 : ℝ)) hsqrt_ge
    calc
      |x| / Real.sqrt (blocks3SaddleBReal r) ≤ |x| / r ^ (3 / 2 : ℝ) := hbase
      _ = A * y := by
        dsimp [A, y]
        rw [Real.rpow_neg hr0]
        ring
  have hθ_three : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ 3 := hθ.trans (by norm_num)
  have h2θ_three : |2 * (x / Real.sqrt (blocks3SaddleBReal r))| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have h3θ_three : |3 * (x / Real.sqrt (blocks3SaddleBReal r))| ≤ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith
  have hrem1 := expLocalRemainderFifth_norm_le hθ_three
  have hrem2 := expLocalRemainderFifth_norm_le h2θ_three
  have hrem3 := expLocalRemainderFifth_norm_le h3θ_three
  have hθ5_le : |x / Real.sqrt (blocks3SaddleBReal r)| ^ 5 ≤ (A * y) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hθ_abs_le 5
  have h2θ5_le :
      |2 * (x / Real.sqrt (blocks3SaddleBReal r))| ^ 5 ≤ (2 * A * y) ^ 5 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa [mul_assoc] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |x / Real.sqrt (blocks3SaddleBReal r)|)
        (mul_le_mul_of_nonneg_left hθ_abs_le (by norm_num)) 5
  have h3θ5_le :
      |3 * (x / Real.sqrt (blocks3SaddleBReal r))| ^ 5 ≤ (3 * A * y) ^ 5 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    simpa [mul_assoc] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 3 * |x / Real.sqrt (blocks3SaddleBReal r)|)
        (mul_le_mul_of_nonneg_left hθ_abs_le (by norm_num)) 5
  have hmain :
      ‖blocks3ScaledRemainder r x‖ ≤
        r * (Real.exp 3 * (A * y) ^ 5) +
          (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) +
            (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5) := by
    unfold blocks3ScaledRemainder
    calc
      ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r)) +
          (((r ^ 2 / 2 : ℝ) : ℂ) *
            expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r)))) +
            (((r ^ 3 / 6 : ℝ) : ℂ) *
              expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖
          ≤ ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r))‖ +
              ‖(((r ^ 2 / 2 : ℝ) : ℂ) *
                expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ +
                ‖(((r ^ 3 / 6 : ℝ) : ℂ) *
                  expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ := by
            calc
              ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r)) +
                  (((r ^ 2 / 2 : ℝ) : ℂ) *
                    expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r)))) +
                    (((r ^ 3 / 6 : ℝ) : ℂ) *
                      expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖
                  ≤ ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r)) +
                      (((r ^ 2 / 2 : ℝ) : ℂ) *
                        expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ +
                        ‖(((r ^ 3 / 6 : ℝ) : ℂ) *
                          expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ :=
                    norm_add_le _ _
              _ ≤ (‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (blocks3SaddleBReal r))‖ +
                    ‖(((r ^ 2 / 2 : ℝ) : ℂ) *
                      expLocalRemainderFifth (2 * (x / Real.sqrt (blocks3SaddleBReal r))))‖) +
                    ‖(((r ^ 3 / 6 : ℝ) : ℂ) *
                      expLocalRemainderFifth (3 * (x / Real.sqrt (blocks3SaddleBReal r))))‖ :=
                  add_le_add (norm_add_le _ _) (le_refl _)
              _ = _ := by ring
      _ ≤ r * (Real.exp 3 * (A * y) ^ 5) +
            (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) +
              (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5) := by
          gcongr
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
            exact mul_le_mul_of_nonneg_left
              (hrem1.trans (mul_le_mul_of_nonneg_left hθ5_le (Real.exp_pos 3).le))
              hr0
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hcoef : 0 ≤ r ^ 2 / 2 := by positivity
            rw [abs_of_nonneg hcoef]
            exact mul_le_mul_of_nonneg_left
              (hrem2.trans (mul_le_mul_of_nonneg_left h2θ5_le (Real.exp_pos 3).le))
              hcoef
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hcoef : 0 ≤ r ^ 3 / 6 := by positivity
            rw [abs_of_nonneg hcoef]
            exact mul_le_mul_of_nonneg_left
              (hrem3.trans (mul_le_mul_of_nonneg_left h3θ5_le (Real.exp_pos 3).le))
              hcoef
  calc
    ‖blocks3ScaledRemainder r x‖
        ≤ r * (Real.exp 3 * (A * y) ^ 5) +
          (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) +
            (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5) := hmain
    _ ≤ blocks3LocalTaylorConst * D * y ^ 5 := by
      have hterm1 : r * (Real.exp 3 * (A * y) ^ 5) ≤
          Real.exp 3 * D * y ^ 5 := by
        calc
          r * (Real.exp 3 * (A * y) ^ 5)
              = Real.exp 3 * (r * A ^ 5) * y ^ 5 := by ring
          _ ≤ Real.exp 3 * D * y ^ 5 := by
            gcongr
      have hterm2 : (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) ≤
          16 * Real.exp 3 * D * y ^ 5 := by
        calc
          (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5)
              = 16 * Real.exp 3 * (r ^ 2 * A ^ 5) * y ^ 5 := by ring
          _ ≤ 16 * Real.exp 3 * D * y ^ 5 := by
            gcongr
      have hterm3 : (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5) ≤
          100 * Real.exp 3 * D * y ^ 5 := by
        calc
          (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5)
              = (81 / 2 : ℝ) * Real.exp 3 * (r ^ 3 * A ^ 5) * y ^ 5 := by ring
          _ ≤ 100 * Real.exp 3 * D * y ^ 5 := by
            gcongr
            norm_num
      unfold blocks3LocalTaylorConst
      calc
        r * (Real.exp 3 * (A * y) ^ 5) +
            (r ^ 2 / 2) * (Real.exp 3 * (2 * A * y) ^ 5) +
              (r ^ 3 / 6) * (Real.exp 3 * (3 * A * y) ^ 5)
            ≤ Real.exp 3 * D * y ^ 5 +
                16 * Real.exp 3 * D * y ^ 5 +
                  100 * Real.exp 3 * D * y ^ 5 :=
              add_le_add (add_le_add hterm1 hterm2) hterm3
        _ ≤ 10000 * Real.exp 3 * D * y ^ 5 := by
          have hnonneg : 0 ≤ Real.exp 3 * D * y ^ 5 := by positivity
          nlinarith

private lemma complex_exp_second_error_bound (C Q R W : ℂ)
    (hW : W = C + Q + R) (hWnorm : ‖W‖ ≤ 1) :
    ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
      Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
        (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
  have hsum :
      (∑ m ∈ Finset.range 3, W ^ m / (m.factorial : ℂ)) =
        1 + W + W ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  have htail :
      ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ ≤ Real.exp 1 * ‖W‖ ^ 3 := by
    calc
      ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ =
          ‖Complex.exp W - ∑ m ∈ Finset.range 3, W ^ m / (m.factorial : ℂ)‖ := by
            rw [hsum]
      _ ≤ ‖W‖ ^ 3 * Real.exp ‖W‖ :=
        Complex.norm_exp_sub_sum_le_norm_mul_exp W 3
      _ ≤ ‖W‖ ^ 3 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hWnorm) (pow_nonneg (norm_nonneg W) 3)
      _ = Real.exp 1 * ‖W‖ ^ 3 := by ring
  have hdecomp :
      Complex.exp W - (1 + C + Q + C ^ 2 / 2) =
        (Complex.exp W - (1 + W + W ^ 2 / 2)) +
          (R + (W ^ 2 - C ^ 2) / 2) := by
    rw [hW]
    ring
  rw [hdecomp]
  calc
    ‖(Complex.exp W - (1 + W + W ^ 2 / 2)) + (R + (W ^ 2 - C ^ 2) / 2)‖
        ≤ ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ +
            ‖R + (W ^ 2 - C ^ 2) / 2‖ := norm_add_le _ _
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R + (W ^ 2 - C ^ 2) / 2‖ :=
      add_le_add htail (le_refl _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + (‖R‖ + ‖(W ^ 2 - C ^ 2) / 2‖) := by
      exact add_le_add (le_refl _) (norm_add_le _ _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + (‖R‖ + ‖W ^ 2 - C ^ 2‖) := by
      have hhalf : ‖(W ^ 2 - C ^ 2) / 2‖ ≤ ‖W ^ 2 - C ^ 2‖ := by
        rw [norm_div, Complex.norm_ofNat]
        norm_num
      exact add_le_add (le_refl _) (add_le_add_right hhalf _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
          (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
      have hsq :
          W ^ 2 - C ^ 2 = (Q + R) * (2 * C + Q + R) := by
        rw [hW]
        ring
      have hprod :
          ‖W ^ 2 - C ^ 2‖ ≤ (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
        rw [hsq]
        calc
          ‖(Q + R) * (2 * C + Q + R)‖ =
              ‖Q + R‖ * ‖2 * C + Q + R‖ := by rw [norm_mul]
          _ ≤ (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
            have hQR : ‖Q + R‖ ≤ ‖Q‖ + ‖R‖ := norm_add_le _ _
            have h2C : ‖(2 : ℂ) * C‖ = 2 * ‖C‖ := by
              rw [norm_mul, Complex.norm_ofNat]
            have hCQR : ‖2 * C + Q + R‖ ≤ 2 * ‖C‖ + ‖Q‖ + ‖R‖ := by
              calc
                ‖2 * C + Q + R‖ ≤ ‖2 * C + Q‖ + ‖R‖ := norm_add_le _ _
                _ ≤ (‖2 * C‖ + ‖Q‖) + ‖R‖ :=
                  add_le_add (norm_add_le _ _) (le_refl _)
                _ = 2 * ‖C‖ + ‖Q‖ + ‖R‖ := by rw [h2C]
            exact mul_le_mul hQR hCQR (norm_nonneg _) (by positivity)
      nlinarith [hprod]

private def blocks3GaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 +
      |x| ^ 11 + |x| ^ 12 + |x| ^ 13 + |x| ^ 14 + |x| ^ 15)

private lemma blocks3GaussianDom_nonneg (x : ℝ) : 0 ≤ blocks3GaussianDom x := by
  unfold blocks3GaussianDom
  positivity

private lemma gaussian_abs_monomial_integrable (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ k) := by
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hk : (-1 : ℝ) < (k : ℝ) := by linarith
  have hbase : Integrable (fun x : ℝ => x ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) hk)
  have hbase2 : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ k) := by
    convert hbase using 1
    ext x
    ring_nf
  have hnorm := hbase2.norm
  convert hnorm using 1
  ext x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]

private lemma blocks3GaussianDom_integrable : Integrable blocks3GaussianDom := by
  let g : ℕ → ℝ → ℝ := fun k x => Real.exp (-(x ^ 2) / 2) * |x| ^ k
  have hsum :
      Integrable (fun x : ℝ =>
        g 5 x + g 6 x + g 7 x + g 8 x + g 9 x + g 10 x +
          g 11 x + g 12 x + g 13 x + g 14 x + g 15 x) := by
    simpa [g, add_assoc] using
      ((((((((((gaussian_abs_monomial_integrable 5).add
        (gaussian_abs_monomial_integrable 6)).add
        (gaussian_abs_monomial_integrable 7)).add
        (gaussian_abs_monomial_integrable 8)).add
        (gaussian_abs_monomial_integrable 9)).add
        (gaussian_abs_monomial_integrable 10)).add
        (gaussian_abs_monomial_integrable 11)).add
        (gaussian_abs_monomial_integrable 12)).add
        (gaussian_abs_monomial_integrable 13)).add
        (gaussian_abs_monomial_integrable 14)).add
        (gaussian_abs_monomial_integrable 15)
  convert hsum using 1
  ext x
  unfold blocks3GaussianDom
  dsimp [g]
  ring_nf

private lemma blocks3GaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, blocks3GaussianDom x := by
  exact integral_nonneg (fun x => blocks3GaussianDom_nonneg x)

private def blocks3LocalL1Const : ℝ :=
  27 * Real.exp 1 * (20 + blocks3LocalTaylorConst) ^ 3 + blocks3LocalTaylorConst +
    6 * (10 + blocks3LocalTaylorConst) * (30 + blocks3LocalTaylorConst)

private lemma blocks3LocalL1Const_pos : 0 < blocks3LocalL1Const := by
  unfold blocks3LocalL1Const blocks3LocalTaylorConst
  positivity

private lemma blocks3_local_integrand_bound {r x : ℝ}
    (hr : 1 ≤ r)
    (hθ : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ 1)
    (hWnorm : ‖blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖
      ≤ blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ)) * blocks3GaussianDom x := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
  let C : ℂ := blocks3ScaledCubic r x
  let Q : ℂ := blocks3ScaledQuartic r x
  let R : ℂ := blocks3ScaledRemainder r x
  let W : ℂ := blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r))
  let y : ℝ := |x|
  let A : ℝ := r ^ (-(3 / 2 : ℝ))
  let B : ℝ := r ^ (-(3 : ℝ))
  let D : ℝ := r ^ (-(9 / 2 : ℝ))
  let K : ℝ := blocks3LocalTaylorConst
  let S : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
  let T : ℝ := (10 * y ^ 4 + K * y ^ 5) * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)
  let G : ℝ := y ^ 5 + y ^ 6 + y ^ 7 + y ^ 8 + y ^ 9 + y ^ 10 +
    y ^ 11 + y ^ 12 + y ^ 13 + y ^ 14 + y ^ 15
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact blocks3LocalTaylorConst_pos.le
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact abs_nonneg x
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hD_nonneg : 0 ≤ D := by dsimp [D]; positivity
  have hA_le_one : A ≤ 1 := by
    dsimp [A]
    rw [Real.rpow_neg hr0]
    have hbase : 1 ≤ r ^ (3 / 2 : ℝ) := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ (3 / 2 : ℝ) := by rw [Real.one_rpow]
        _ ≤ r ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow zero_le_one hr (by norm_num : (0 : ℝ) ≤ 3 / 2)
    exact inv_le_one_of_one_le₀ hbase
  have hA_mul_A : A * A = B := by
    dsimp [A, B]
    rw [← Real.rpow_add hrpos]
    norm_num
  have hA_mul_B : A * B = D := by
    dsimp [A, B, D]
    rw [← Real.rpow_add hrpos]
    norm_num
  have hB_le_A : B ≤ A := by
    rw [← hA_mul_A]
    exact mul_le_of_le_one_right hA_nonneg hA_le_one
  have hB_le_one : B ≤ 1 := hB_le_A.trans hA_le_one
  have hD_le_A : D ≤ A := by
    rw [← hA_mul_B]
    exact mul_le_of_le_one_right hA_nonneg hB_le_one
  have hD_le_B : D ≤ B := by
    rw [← hA_mul_B]
    exact mul_le_of_le_one_left hB_nonneg hA_le_one
  have hWsplit : W = C + Q + R := by
    dsimp [W, C, Q, R]
    exact blocks3LocalExponent_scaled_split hbpos
  have hP :
      saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x =
        1 + C + Q + C ^ 2 / 2 := by
    dsimp [C, Q]
    exact blocks3_saddleSecondPoly_eq_scaled_terms hbpos
  have herr := complex_exp_second_error_bound C Q R W hWsplit (by simpa [W] using hWnorm)
  have hC : ‖C‖ ≤ 10 * A * y ^ 3 := by
    dsimp [C, A, y]
    simpa [mul_assoc] using blocks3ScaledCubic_norm_le (r := r) (x := x) hr
  have hQ_B : ‖Q‖ ≤ 10 * B * y ^ 4 := by
    dsimp [Q, B, y]
    simpa [mul_assoc] using blocks3ScaledQuartic_norm_le (r := r) (x := x) hr
  have hQ_A : ‖Q‖ ≤ 10 * A * y ^ 4 := by
    exact hQ_B.trans (by gcongr)
  have hR_D : ‖R‖ ≤ K * D * y ^ 5 := by
    dsimp [R, K, D, y]
    simpa [mul_assoc] using blocks3ScaledRemainder_norm_le (r := r) (x := x) hr hθ
  have hR_A : ‖R‖ ≤ K * A * y ^ 5 := by
    exact hR_D.trans (by gcongr)
  have hR_B : ‖R‖ ≤ K * B * y ^ 5 := by
    exact hR_D.trans (by gcongr)
  have hWpoly : ‖W‖ ≤ A * S := by
    calc
      ‖W‖ = ‖C + Q + R‖ := by rw [hWsplit]
      _ ≤ ‖C‖ + ‖Q‖ + ‖R‖ := by
        calc
          ‖C + Q + R‖ ≤ ‖C + Q‖ + ‖R‖ := norm_add_le _ _
          _ ≤ (‖C‖ + ‖Q‖) + ‖R‖ := add_le_add (norm_add_le _ _) (le_refl _)
          _ = ‖C‖ + ‖Q‖ + ‖R‖ := by ring
      _ ≤ 10 * A * y ^ 3 + 10 * A * y ^ 4 + K * A * y ^ 5 :=
        add_le_add (add_le_add hC hQ_A) hR_A
      _ = A * S := by
        dsimp [S]
        ring
  have hWcube :
      Real.exp 1 * ‖W‖ ^ 3 ≤ Real.exp 1 * D * S ^ 3 := by
    have hA_cube : A ^ 3 = D := by
      dsimp [A, D]
      rw [(Real.rpow_mul_natCast hr0 (-(3 / 2 : ℝ)) 3).symm]
      norm_num
    calc
      Real.exp 1 * ‖W‖ ^ 3 ≤ Real.exp 1 * (A * S) ^ 3 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg W) hWpoly 3) (Real.exp_pos 1).le
      _ = Real.exp 1 * D * S ^ 3 := by
        rw [mul_pow, hA_cube]
        ring
  have hQR : ‖Q‖ + ‖R‖ ≤ B * (10 * y ^ 4 + K * y ^ 5) := by
    calc
      ‖Q‖ + ‖R‖ ≤ 10 * B * y ^ 4 + K * B * y ^ 5 := add_le_add hQ_B hR_B
      _ = B * (10 * y ^ 4 + K * y ^ 5) := by ring
  have hCQR : 2 * ‖C‖ + ‖Q‖ + ‖R‖ ≤ A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5) := by
    calc
      2 * ‖C‖ + ‖Q‖ + ‖R‖
          ≤ 2 * (10 * A * y ^ 3) + 10 * A * y ^ 4 + K * A * y ^ 5 := by
            exact add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)) hQ_A) hR_A
      _ = A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5) := by ring
  have hprod :
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) ≤ D * T := by
    calc
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖)
          ≤ (B * (10 * y ^ 4 + K * y ^ 5)) *
              (A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) := by
            have hupper_nonneg : 0 ≤ B * (10 * y ^ 4 + K * y ^ 5) := by
              positivity
            exact mul_le_mul hQR hCQR (by positivity) hupper_nonneg
      _ = D * T := by
        dsimp [T]
        rw [show B * (10 * y ^ 4 + K * y ^ 5) *
              (A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) =
              (A * B) * ((10 * y ^ 4 + K * y ^ 5) *
                (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) by ring]
        rw [hA_mul_B]
  have hpoly :
      Real.exp 1 * S ^ 3 + K * y ^ 5 + T ≤ blocks3LocalL1Const * G := by
    have hK20_nonneg : 0 ≤ 20 + K := by positivity
    have hK10_nonneg : 0 ≤ 10 + K := by positivity
    have hK30_nonneg : 0 ≤ 30 + K := by positivity
    have hG_nonneg : 0 ≤ G := by
      dsimp [G]
      positivity
    have hy5_le_G : y ^ 5 ≤ G := by
      dsimp [G]
      nlinarith [pow_nonneg hy0 6, pow_nonneg hy0 7, pow_nonneg hy0 8,
        pow_nonneg hy0 9, pow_nonneg hy0 10, pow_nonneg hy0 11,
        pow_nonneg hy0 12, pow_nonneg hy0 13, pow_nonneg hy0 14,
        pow_nonneg hy0 15]
    have hcube_support :
        (y ^ 3 + y ^ 4 + y ^ 5) ^ 3 ≤ 27 * G := by
      dsimp [G]
      ring_nf
      nlinarith [pow_nonneg hy0 5, pow_nonneg hy0 6, pow_nonneg hy0 7,
        pow_nonneg hy0 8, pow_nonneg hy0 9, pow_nonneg hy0 10,
        pow_nonneg hy0 11, pow_nonneg hy0 12, pow_nonneg hy0 13,
        pow_nonneg hy0 14, pow_nonneg hy0 15]
    have hprod_support :
        (y ^ 4 + y ^ 5) * (y ^ 3 + y ^ 4 + y ^ 5) ≤ 6 * G := by
      dsimp [G]
      ring_nf
      nlinarith [pow_nonneg hy0 5, pow_nonneg hy0 6, pow_nonneg hy0 7,
        pow_nonneg hy0 8, pow_nonneg hy0 9, pow_nonneg hy0 10]
    have hS_le : S ≤ (20 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by
      dsimp [S]
      calc
        10 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
            ≤ (20 + K) * y ^ 3 + (20 + K) * y ^ 4 + (20 + K) * y ^ 5 := by
              gcongr
              · linarith
              · linarith
              · linarith
        _ = (20 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by ring
    have hS_cube :
        S ^ 3 ≤ (20 + K) ^ 3 * (27 * G) := by
      calc
        S ^ 3 ≤ ((20 + K) * (y ^ 3 + y ^ 4 + y ^ 5)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hS_le 3
        _ = (20 + K) ^ 3 * (y ^ 3 + y ^ 4 + y ^ 5) ^ 3 := by ring
        _ ≤ (20 + K) ^ 3 * (27 * G) :=
          mul_le_mul_of_nonneg_left hcube_support (pow_nonneg hK20_nonneg 3)
    have hT_le :
        T ≤ (10 + K) * (30 + K) * (6 * G) := by
      have hleft : 10 * y ^ 4 + K * y ^ 5 ≤ (10 + K) * (y ^ 4 + y ^ 5) := by
        calc
          10 * y ^ 4 + K * y ^ 5 ≤ (10 + K) * y ^ 4 + (10 + K) * y ^ 5 := by
            gcongr
            · linarith
            · linarith
          _ = (10 + K) * (y ^ 4 + y ^ 5) := by ring
      have hright :
          20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5 ≤
            (30 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by
        calc
          20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
              ≤ (30 + K) * y ^ 3 + (30 + K) * y ^ 4 + (30 + K) * y ^ 5 := by
                gcongr
                · linarith
                · linarith
                · linarith
          _ = (30 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by ring
      calc
        T ≤ ((10 + K) * (y ^ 4 + y ^ 5)) *
              ((30 + K) * (y ^ 3 + y ^ 4 + y ^ 5)) := by
          dsimp [T]
          exact mul_le_mul hleft hright (by positivity) (by positivity)
        _ = (10 + K) * (30 + K) *
              ((y ^ 4 + y ^ 5) * (y ^ 3 + y ^ 4 + y ^ 5)) := by ring
        _ ≤ (10 + K) * (30 + K) * (6 * G) := by
          gcongr
    calc
      Real.exp 1 * S ^ 3 + K * y ^ 5 + T
          ≤ Real.exp 1 * ((20 + K) ^ 3 * (27 * G)) + K * G +
              (10 + K) * (30 + K) * (6 * G) := by
            exact add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left hS_cube (Real.exp_pos 1).le)
              (mul_le_mul_of_nonneg_left hy5_le_G hK_nonneg)) hT_le
      _ = (27 * Real.exp 1 * (20 + K) ^ 3 + K +
            6 * (10 + K) * (30 + K)) * G := by ring
      _ = blocks3LocalL1Const * G := by
        dsimp [K]
        unfold blocks3LocalL1Const
        ring
  have hdiff :
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
        blocks3LocalL1Const * D * G := by
    calc
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
          ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
              (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := herr
      _ ≤ Real.exp 1 * D * S ^ 3 + K * D * y ^ 5 + D * T := by
        exact add_le_add (add_le_add hWcube hR_D) hprod
      _ = D * (Real.exp 1 * S ^ 3 + K * y ^ 5 + T) := by ring
      _ ≤ D * (blocks3LocalL1Const * G) :=
        mul_le_mul_of_nonneg_left hpoly hD_nonneg
      _ = blocks3LocalL1Const * D * G := by ring
  rw [blocks3_saddleLocalRatio_eq]
  rw [hP]
  change
    ‖Complex.exp (-(x ^ 2) / 2) *
        (Complex.exp W - (1 + C + Q + C ^ 2 / 2))‖ ≤
      blocks3LocalL1Const * D * blocks3GaussianDom x
  rw [norm_mul]
  have hgauss :
      ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  rw [hgauss]
  unfold blocks3GaussianDom
  dsimp [D, G, y]
  calc
    Real.exp (-(x ^ 2) / 2) *
        ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
        ≤ Real.exp (-(x ^ 2) / 2) * (blocks3LocalL1Const * D * G) :=
          mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ = blocks3LocalL1Const * D *
        (Real.exp (-(x ^ 2) / 2) *
          (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 +
            |x| ^ 11 + |x| ^ 12 + |x| ^ 13 + |x| ^ 14 + |x| ^ 15)) := by
      ring

private lemma blocks3_local_integrand_continuous (r : ℝ) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖ := by
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r))) -
            saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖ := by
    unfold blocks3LocalExponent ExpStirling.expLocalRemainder saddleSecondPoly
    fun_prop
  simpa [blocks3_saddleLocalRatio_eq] using h

private lemma blocks3GaussianDom_continuous : Continuous blocks3GaussianDom := by
  unfold blocks3GaussianDom
  fun_prop

private lemma blocks3GaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, blocks3GaussianDom x) ≤ ∫ x : ℝ, blocks3GaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral blocks3GaussianDom_integrable
    (Eventually.of_forall blocks3GaussianDom_nonneg)

theorem blocks3_local_second_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖) /
          blocks3SecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, blocks3GaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact blocks3GaussianDom_integral_nonneg
  have hupper_tendsto :
      Tendsto
        (fun r : ℝ => blocks3LocalL1Const * M * r ^ (-(3 / 2 : ℝ)))
        atTop (𝓝 0) := by
    have hpow : Tendsto (fun r : ℝ => r ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)
    simpa [mul_assoc] using hpow.const_mul (blocks3LocalL1Const * M)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3SecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3_delta_le_one_eventually,
      blocks3_local_exponent_norm_le_eventually,
      blocks3LocalBound_tendsto_zero.eventually_le_const zero_lt_one,
      blocks3SecondCorrScale_pos_eventually] with
      r hr hδle hloc hlocSmall hcorrPos
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖
    let H : ℝ → ℝ := fun x =>
      (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * blocks3GaussianDom x
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one hr
    have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ H x := by
      intro x hx
      have hxabs : |x| ≤ L := by
        exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hθδ : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ blocks3SaddleDeltaReal r := by
        rw [abs_div, abs_of_pos hsqrt_pos]
        calc
          |x| / Real.sqrt (blocks3SaddleBReal r) ≤
              L / Real.sqrt (blocks3SaddleBReal r) :=
            div_le_div_of_nonneg_right hxabs hsqrt_pos.le
          _ = blocks3SaddleDeltaReal r := by
            dsimp [L]
            field_simp [hsqrt_pos.ne']
      have hθone : |x / Real.sqrt (blocks3SaddleBReal r)| ≤ 1 := hθδ.trans hδle
      have hWnorm :
          ‖blocks3LocalExponent r (x / Real.sqrt (blocks3SaddleBReal r))‖ ≤ 1 :=
        (hloc (x / Real.sqrt (blocks3SaddleBReal r)) hθδ).trans hlocSmall
      have hb := blocks3_local_integrand_bound hr hθone hWnorm
      dsimp [F, H]
      exact hb
    have hFint : IntervalIntegrable F volume (-L) L := by
      exact (blocks3_local_integrand_continuous r).intervalIntegrable _ _
    have hHint : IntervalIntegrable H volume (-L) L := by
      exact (blocks3GaussianDom_continuous.const_mul
        (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ)))).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤
          (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M := by
      have hconst_nonneg :
          0 ≤ blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ)) :=
        mul_nonneg blocks3LocalL1Const_pos.le (by positivity)
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, H x :=
          intervalIntegral.integral_mono_on hle hFint hHint hpoint
        _ = (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) *
              (∫ x in -L..L, blocks3GaussianDom x) := by
          dsimp [H]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact blocks3GaussianDom_window_le_integral hLnonneg)
            hconst_nonneg
    have hnum_nonneg :
        0 ≤ (blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M :=
      mul_nonneg
        (mul_nonneg blocks3LocalL1Const_pos.le (by positivity)) hM_nonneg
    have hmain :
        (∫ x in -L..L, F x) / blocks3SecondCorrScale r ≤
          ((blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M) /
            blocks3SecondCorrScale r := by
      exact div_le_div_of_nonneg_right hIntBound hcorrPos.le
    have hpow_div :
        r ^ (-(9 / 2 : ℝ)) / blocks3SecondCorrScale r =
          r ^ (-(3 / 2 : ℝ)) := by
      unfold blocks3SecondCorrScale
      rw [div_eq_mul_inv]
      have hneg3 : r ^ (-(3 : ℝ)) = (r ^ (3 : ℝ))⁻¹ :=
        Real.rpow_neg hrpos.le (3 : ℝ)
      rw [hneg3, inv_inv]
      rw [← Real.rpow_add hrpos]
      norm_num
    calc
      ((∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖) /
          blocks3SecondCorrScale r)
          = (∫ x in -L..L, F x) / blocks3SecondCorrScale r := by rfl
      _ ≤ ((blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M) /
            blocks3SecondCorrScale r := hmain
      _ = blocks3LocalL1Const * M * r ^ (-(3 / 2 : ℝ)) := by
        rw [show ((blocks3LocalL1Const * r ^ (-(9 / 2 : ℝ))) * M) /
            blocks3SecondCorrScale r =
            blocks3LocalL1Const * M *
              (r ^ (-(9 / 2 : ℝ)) / blocks3SecondCorrScale r) by ring]
        rw [hpow_div]

/-- The produced second-order H-admissible instance for blocks of size at most three. -/
def blocks3SecondOrderHAdmissible : SecondOrderHAdmissible blocks3HAdmissible where
  b3 := blocks3SaddleB3Real
  b4 := blocks3SaddleB4Real
  corrScale := blocks3SecondCorrScale
  corrScale_pos := by
    simpa [blocks3HAdmissible] using blocks3SecondCorrScale_pos_eventually
  corrScale_tendsto_zero := by
    simpa [blocks3HAdmissible] using blocks3SecondCorrScale_tendsto_zero
  corrScale_dominates_correction := by
    refine ⟨1000000, by norm_num, ?_⟩
    simpa [blocks3HAdmissible] using blocks3_saddleCorrectionScale_le_secondCorrScale_eventually
  local_second_L1 := by
    simpa [blocks3HAdmissible] using blocks3_local_second_L1
  tail_second_uniform := by
    simpa [blocks3HAdmissible] using blocks3_tail_second_uniform

end Blocks3HAdmissible
end
end

/-!
# Third-order saddle data for blocks of size at most three

This file instantiates the third-order Hayman wrapper for
`exp (z + z^2 / 2 + z^3 / 6)`.  The fifth and sixth logarithmic saddle
derivatives are
`b_5(r)=r+16r^2+81r^3/2` and `b_6(r)=r+32r^2+243r^3/2`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false

noncomputable section

namespace Blocks3HAdmissible

private lemma blocks3SaddleBReal_pos_of_ge_one_p2m2 {r : ℝ} (hr : 1 ≤ r) :
    0 < blocks3SaddleBReal r := by
  unfold blocks3SaddleBReal
  positivity

private lemma blocks3_b_ge_r_sq {r : ℝ} (hr : 1 ≤ r) :
    r ^ 2 ≤ blocks3SaddleBReal r := by
  unfold blocks3SaddleBReal
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]

private lemma blocks3_b_ge_r_cubed {r : ℝ} (hr : 1 ≤ r) :
    r ^ 3 ≤ blocks3SaddleBReal r := by
  unfold blocks3SaddleBReal
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 2 by positivity,
    show 0 ≤ r ^ 3 by positivity]

private lemma blocks3_sqrtB_sq_p2m2 {r : ℝ} (hb : 0 < blocks3SaddleBReal r) :
    (Real.sqrt (blocks3SaddleBReal r)) ^ 2 = blocks3SaddleBReal r :=
  Real.sq_sqrt hb.le

private lemma blocks3_sqrtB_ge_r {r : ℝ} (hr : 1 ≤ r) :
    r ≤ Real.sqrt (blocks3SaddleBReal r) := by
  exact Real.le_sqrt_of_sq_le (blocks3_b_ge_r_sq hr)

private lemma blocks3_b_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(blocks3SaddleBReal r : ℂ)‖ = blocks3SaddleBReal r := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one_p2m2 hr
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]

private lemma blocks3_sqrtB_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(Real.sqrt (blocks3SaddleBReal r) : ℂ)‖ =
      Real.sqrt (blocks3SaddleBReal r) := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one_p2m2 hr
  have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt_pos]

private lemma blocks3_one_le_r_sq {r : ℝ} (hr : 1 ≤ r) : 1 ≤ r ^ 2 := by
  nlinarith [sq_nonneg (r - 1)]

private lemma blocks3_r_sq_le_r_cubed {r : ℝ} (hr : 1 ≤ r) : r ^ 2 ≤ r ^ 3 := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  calc
    r ^ 2 = r ^ 2 * 1 := by ring
    _ ≤ r ^ 2 * r := mul_le_mul_of_nonneg_left hr (sq_nonneg r)
    _ = r ^ 3 := by ring

private lemma blocks3_r_le_r_cubed {r : ℝ} (hr : 1 ≤ r) : r ≤ r ^ 3 := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  calc
    r = r * 1 := by ring
    _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left (blocks3_one_le_r_sq hr) hr0
    _ = r ^ 3 := by ring

private lemma blocks3_b3_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ blocks3SaddleB3Real r := by
  unfold blocks3SaddleB3Real
  positivity

private lemma blocks3_b4_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ blocks3SaddleB4Real r := by
  unfold blocks3SaddleB4Real
  positivity

private lemma blocks3_b5_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ blocks3SaddleB5Real r := by
  unfold blocks3SaddleB5Real
  positivity

private lemma blocks3_b6_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ blocks3SaddleB6Real r := by
  unfold blocks3SaddleB6Real
  positivity

private lemma blocks3_b3_le {r : ℝ} (hr : 1 ≤ r) :
    blocks3SaddleB3Real r ≤ 10 * r ^ 3 := by
  unfold blocks3SaddleB3Real
  nlinarith [blocks3_r_le_r_cubed hr, blocks3_r_sq_le_r_cubed hr]

private lemma blocks3_b4_le {r : ℝ} (hr : 1 ≤ r) :
    blocks3SaddleB4Real r ≤ 25 * r ^ 3 := by
  unfold blocks3SaddleB4Real
  nlinarith [blocks3_r_le_r_cubed hr, blocks3_r_sq_le_r_cubed hr]

private lemma blocks3_b5_le {r : ℝ} (hr : 1 ≤ r) :
    blocks3SaddleB5Real r ≤ 60 * r ^ 3 := by
  unfold blocks3SaddleB5Real
  nlinarith [blocks3_r_le_r_cubed hr, blocks3_r_sq_le_r_cubed hr]

private lemma blocks3_b6_le {r : ℝ} (hr : 1 ≤ r) :
    blocks3SaddleB6Real r ≤ 160 * r ^ 3 := by
  unfold blocks3SaddleB6Real
  nlinarith [blocks3_r_le_r_cubed hr, blocks3_r_sq_le_r_cubed hr]

private lemma blocks3_b_pow_three_ge_r_pow_nine {r : ℝ} (hr : 1 ≤ r) :
    r ^ 9 ≤ (blocks3SaddleBReal r) ^ 3 := by
  have hb_ge := blocks3_b_ge_r_cubed hr
  calc
    r ^ 9 = (r ^ 3) ^ 3 := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hb_ge 3

private lemma blocks3_b_pow_four_ge_r_pow_twelve {r : ℝ} (hr : 1 ≤ r) :
    r ^ 12 ≤ (blocks3SaddleBReal r) ^ 4 := by
  have hb_ge := blocks3_b_ge_r_cubed hr
  calc
    r ^ 12 = (r ^ 3) ^ 4 := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hb_ge 4

private lemma blocks3_b_pow_five_ge_r_pow_fifteen {r : ℝ} (hr : 1 ≤ r) :
    r ^ 15 ≤ (blocks3SaddleBReal r) ^ 5 := by
  have hb_ge := blocks3_b_ge_r_cubed hr
  calc
    r ^ 15 = (r ^ 3) ^ 5 := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 5 :=
      pow_le_pow_left₀ (by positivity) hb_ge 5

private lemma blocks3_b_pow_six_ge_r_pow_eighteen {r : ℝ} (hr : 1 ≤ r) :
    r ^ 18 ≤ (blocks3SaddleBReal r) ^ 6 := by
  have hb_ge := blocks3_b_ge_r_cubed hr
  calc
    r ^ 18 = (r ^ 3) ^ 6 := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 6 :=
      pow_le_pow_left₀ (by positivity) hb_ge 6

private lemma blocks3_sqrtB_pow_five_ge_r_pow_seven {r : ℝ} (hr : 1 ≤ r) :
    r ^ 7 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 5 := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one_p2m2 hr
  have hb2_ge : r ^ 6 ≤ (blocks3SaddleBReal r) ^ 2 := by
    have hb_ge := blocks3_b_ge_r_cubed hr
    calc
      r ^ 6 = (r ^ 3) ^ 2 := by ring
      _ ≤ (blocks3SaddleBReal r) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hb_ge 2
  have hsqrt_ge := blocks3_sqrtB_ge_r hr
  calc
    r ^ 7 = r ^ 6 * r := by ring
    _ ≤ (blocks3SaddleBReal r) ^ 2 * Real.sqrt (blocks3SaddleBReal r) :=
      mul_le_mul hb2_ge hsqrt_ge (by positivity) (by positivity)
    _ = (Real.sqrt (blocks3SaddleBReal r)) ^ 5 := by
      let s : ℝ := Real.sqrt (blocks3SaddleBReal r)
      change (blocks3SaddleBReal r) ^ 2 * s = s ^ 5
      have hs : s ^ 2 = blocks3SaddleBReal r := by
        dsimp [s]
        exact blocks3_sqrtB_sq_p2m2 hbpos
      rw [← hs]
      ring

private lemma blocks3_sqrtB_pow_three_mul_b_pow_two_ge_r_pow_ten {r : ℝ}
    (hr : 1 ≤ r) :
    r ^ 10 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 3 *
      (blocks3SaddleBReal r) ^ 2 := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one_p2m2 hr
  have hb3_ge := blocks3_b_pow_three_ge_r_pow_nine hr
  have hsqrt_ge := blocks3_sqrtB_ge_r hr
  calc
    r ^ 10 = r * r ^ 9 := by ring
    _ ≤ Real.sqrt (blocks3SaddleBReal r) * (blocks3SaddleBReal r) ^ 3 :=
      mul_le_mul hsqrt_ge hb3_ge (by positivity) (by positivity)
    _ = (Real.sqrt (blocks3SaddleBReal r)) ^ 3 *
        (blocks3SaddleBReal r) ^ 2 := by
      let s : ℝ := Real.sqrt (blocks3SaddleBReal r)
      change s * (blocks3SaddleBReal r) ^ 3 = s ^ 3 * (blocks3SaddleBReal r) ^ 2
      have hs : s ^ 2 = blocks3SaddleBReal r := by
        dsimp [s]
        exact blocks3_sqrtB_sq_p2m2 hbpos
      rw [← hs]
      ring

private lemma blocks3_sqrtB_pow_nine_ge_r_pow_thirteen {r : ℝ} (hr : 1 ≤ r) :
    r ^ 13 ≤ (Real.sqrt (blocks3SaddleBReal r)) ^ 9 := by
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one_p2m2 hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have hsqrt_ge := blocks3_sqrtB_ge_r hr
  calc
    r ^ 13 = r * r ^ 12 := by ring
    _ ≤ Real.sqrt (blocks3SaddleBReal r) * (blocks3SaddleBReal r) ^ 4 :=
      mul_le_mul hsqrt_ge hb4_ge (by positivity) (by positivity)
    _ = (Real.sqrt (blocks3SaddleBReal r)) ^ 9 := by
      let s : ℝ := Real.sqrt (blocks3SaddleBReal r)
      change s * (blocks3SaddleBReal r) ^ 4 = s ^ 9
      have hs : s ^ 2 = blocks3SaddleBReal r := by
        dsimp [s]
        exact blocks3_sqrtB_sq_p2m2 hbpos
      rw [← hs]
      ring

private lemma blocks3_rpow_neg_three_eq_inv_cube {r : ℝ} (hr : 0 < r) :
    r ^ (-(3 : ℝ)) = (r ^ 3)⁻¹ := by
  simpa using Real.rpow_neg hr.le (3 : ℝ)

private lemma blocks3_term_b6_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    |blocks3SaddleB6Real r| / (blocks3SaddleBReal r) ^ 3 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb3_ge := blocks3_b_pow_three_ge_r_pow_nine hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  rw [abs_of_nonneg (blocks3_b6_nonneg_of_ge_one hr)]
  calc
    blocks3SaddleB6Real r / (blocks3SaddleBReal r) ^ 3
        ≤ (160 * r ^ 3) / r ^ 9 := by
          exact div_le_div₀ (by positivity) (blocks3_b6_le hr) (by positivity)
            (by nlinarith [hb3_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 6 by positivity]

private lemma blocks3_term_b3b5_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    |blocks3SaddleB3Real r * blocks3SaddleB5Real r| /
        (blocks3SaddleBReal r) ^ 4 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have hnum_nonneg : 0 ≤ blocks3SaddleB3Real r * blocks3SaddleB5Real r :=
    mul_nonneg (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b5_nonneg_of_ge_one hr)
  have hnum_le : blocks3SaddleB3Real r * blocks3SaddleB5Real r ≤ 600 * r ^ 6 := by
    calc
      blocks3SaddleB3Real r * blocks3SaddleB5Real r
          ≤ (10 * r ^ 3) * (60 * r ^ 3) :=
            mul_le_mul (blocks3_b3_le hr) (blocks3_b5_le hr)
              (blocks3_b5_nonneg_of_ge_one hr) (by positivity)
      _ = 600 * r ^ 6 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  rw [abs_of_nonneg hnum_nonneg]
  calc
    blocks3SaddleB3Real r * blocks3SaddleB5Real r /
        (blocks3SaddleBReal r) ^ 4
        ≤ (600 * r ^ 6) / r ^ 12 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity)
            (by nlinarith [hb4_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 9 by positivity]

private lemma blocks3_term_b4sq_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    (blocks3SaddleB4Real r) ^ 2 / (blocks3SaddleBReal r) ^ 4 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have hnum_le : (blocks3SaddleB4Real r) ^ 2 ≤ 625 * r ^ 6 := by
    calc
      (blocks3SaddleB4Real r) ^ 2 ≤ (25 * r ^ 3) ^ 2 :=
        pow_le_pow_left₀ (blocks3_b4_nonneg_of_ge_one hr) (blocks3_b4_le hr) 2
      _ = 625 * r ^ 6 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  calc
    (blocks3SaddleB4Real r) ^ 2 / (blocks3SaddleBReal r) ^ 4
        ≤ (625 * r ^ 6) / r ^ 12 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity)
            (by nlinarith [hb4_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 9 by positivity]

private lemma blocks3_term_b3sqb4_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    (blocks3SaddleB3Real r) ^ 2 * |blocks3SaddleB4Real r| /
        (blocks3SaddleBReal r) ^ 5 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb5_ge := blocks3_b_pow_five_ge_r_pow_fifteen hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have hb4_nonneg := blocks3_b4_nonneg_of_ge_one hr
  have hb3sq : (blocks3SaddleB3Real r) ^ 2 ≤ (10 * r ^ 3) ^ 2 :=
    pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 2
  have hnum_le :
      (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r ≤ 2500 * r ^ 9 := by
    calc
      (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r
          ≤ (10 * r ^ 3) ^ 2 * (25 * r ^ 3) :=
            mul_le_mul hb3sq (blocks3_b4_le hr) hb4_nonneg (by positivity)
      _ = 2500 * r ^ 9 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  rw [abs_of_nonneg hb4_nonneg]
  calc
    (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r /
        (blocks3SaddleBReal r) ^ 5
        ≤ (2500 * r ^ 9) / r ^ 15 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity)
            (by nlinarith [hb5_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 12 by positivity]

private lemma blocks3_term_b3four_le_thirdCorrScale {r : ℝ} (hr : 1 ≤ r) :
    (blocks3SaddleB3Real r) ^ 4 / (blocks3SaddleBReal r) ^ 6 ≤
      100000 * blocks3ThirdCorrScale r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb6_ge := blocks3_b_pow_six_ge_r_pow_eighteen hr
  have h1_le_r3 : 1 ≤ r ^ 3 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r * r ^ 2 :=
        mul_le_mul hr (blocks3_one_le_r_sq hr) zero_le_one (le_trans zero_le_one hr)
      _ = r ^ 3 := by ring
  have hnum_le : (blocks3SaddleB3Real r) ^ 4 ≤ 10000 * r ^ 12 := by
    calc
      (blocks3SaddleB3Real r) ^ 4 ≤ (10 * r ^ 3) ^ 4 :=
        pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 4
      _ = 10000 * r ^ 12 := by ring
  unfold blocks3ThirdCorrScale blocks3SecondCorrScale
  rw [blocks3_rpow_neg_three_eq_inv_cube hrpos]
  calc
    (blocks3SaddleB3Real r) ^ 4 / (blocks3SaddleBReal r) ^ 6
        ≤ (10000 * r ^ 12) / r ^ 18 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity)
            (by nlinarith [hb6_ge])
    _ ≤ 100000 * (r ^ 3)⁻¹ := by
      field_simp [hrpos.ne']
      nlinarith [h1_le_r3, show 0 ≤ r ^ 15 by positivity]

lemma blocks3_saddleThirdCorrectionScale_le_thirdCorrScale :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in atTop,
        saddleThirdCorrectionScale blocks3SaddleBReal blocks3SaddleB3Real
          blocks3SaddleB4Real blocks3SaddleB5Real blocks3SaddleB6Real r ≤
            K * blocks3ThirdCorrScale r := by
  refine ⟨2000000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
      blocks3_saddleCorrectionScale_le_secondCorrScale_eventually] with r hr hsecond
  have hscale_nonneg : 0 ≤ blocks3ThirdCorrScale r := by
    unfold blocks3ThirdCorrScale blocks3SecondCorrScale
    positivity
  have hterm₁ := blocks3_term_b6_le_thirdCorrScale (r := r) hr
  have hterm₂ := blocks3_term_b3b5_le_thirdCorrScale (r := r) hr
  have hterm₃ := blocks3_term_b4sq_le_thirdCorrScale (r := r) hr
  have hterm₄ := blocks3_term_b3sqb4_le_thirdCorrScale (r := r) hr
  have hterm₅ := blocks3_term_b3four_le_thirdCorrScale (r := r) hr
  have hsecond' :
      saddleCorrectionScale blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r
        ≤ 1000000 * blocks3ThirdCorrScale r := by
    simpa [blocks3ThirdCorrScale] using hsecond
  rw [saddleThirdCorrectionScale_apply]
  nlinarith

private def blocks3ThirdGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
      |x| ^ 9 + |x| ^ 10 + |x| ^ 12)

private lemma blocks3ThirdGaussianDom_nonneg (x : ℝ) :
    0 ≤ blocks3ThirdGaussianDom x := by
  unfold blocks3ThirdGaussianDom
  positivity

private lemma gaussian_abs_monomial_integrable_third (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ k) := by
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hk : (-1 : ℝ) < (k : ℝ) := by linarith
  have hbase : Integrable (fun x : ℝ => x ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) hk)
  have hbase2 : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ k) := by
    convert hbase using 1
    ext x
    ring_nf
  have hnorm := hbase2.norm
  convert hnorm using 1
  ext x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]

private lemma blocks3ThirdGaussianDom_integrable : Integrable blocks3ThirdGaussianDom := by
  unfold blocks3ThirdGaussianDom
  have hsum :
      Integrable
        (((((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 5) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 6)) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 7)) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 8)) +
          ((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 9) +
            (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 10) +
            (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 12))) :=
    ((((gaussian_abs_monomial_integrable_third 5).add
      (gaussian_abs_monomial_integrable_third 6)).add
      (gaussian_abs_monomial_integrable_third 7)).add
      (gaussian_abs_monomial_integrable_third 8)).add
      (((gaussian_abs_monomial_integrable_third 9).add
        (gaussian_abs_monomial_integrable_third 10)).add
        (gaussian_abs_monomial_integrable_third 12))
  convert hsum using 1
  ext x
  simp only [Pi.add_apply]
  ring_nf

private lemma blocks3ThirdGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, blocks3ThirdGaussianDom x := by
  exact integral_nonneg (fun x => blocks3ThirdGaussianDom_nonneg x)

private lemma blocks3ThirdGaussianDom_continuous : Continuous blocks3ThirdGaussianDom := by
  unfold blocks3ThirdGaussianDom
  fun_prop

private lemma blocks3ThirdGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, blocks3ThirdGaussianDom x) ≤ ∫ x : ℝ, blocks3ThirdGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral blocks3ThirdGaussianDom_integrable
    (Eventually.of_forall blocks3ThirdGaussianDom_nonneg)

private lemma blocks3_third_extra5_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((blocks3SaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖ ≤
        10 * |x| ^ 5 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < blocks3SaddleBReal r := blocks3SaddleBReal_pos_of_ge_one_p2m2 hr
  have hsqrt_pos : 0 < Real.sqrt (blocks3SaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt5_ge := blocks3_sqrtB_pow_five_ge_r_pow_seven hr
  have hcoef :
      ‖(blocks3SaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)‖ ≤ 10 / r ^ 4 := by
    calc
      ‖(blocks3SaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)‖
          = blocks3SaddleB5Real r /
              (120 * (Real.sqrt (blocks3SaddleBReal r)) ^ 5) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (blocks3_b5_nonneg_of_ge_one hr)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_sqrtB_norm_eq_of_ge_one hr]
      _ ≤ (60 * r ^ 3) / (120 * r ^ 7) := by
            exact div_le_div₀ (by positivity) (blocks3_b5_le hr) (by positivity)
              (by nlinarith [hsqrt5_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [show 0 ≤ r ^ 7 by positivity]
  calc
    ‖Complex.I * ((blocks3SaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖
        = ‖(blocks3SaddleB5Real r : ℂ) /
            (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)‖ * |x| ^ 5 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 5 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 5)
    _ = 10 * |x| ^ 5 / r ^ 4 := by ring

private lemma blocks3_third_extra6_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖ ≤ 10 * |x| ^ 6 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb3_ge := blocks3_b_pow_three_ge_r_pow_nine hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hcoef :
      ‖(blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)‖
        ≤ 10 / r ^ 4 := by
    calc
      ‖(blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)‖
          = blocks3SaddleB6Real r / (720 * (blocks3SaddleBReal r) ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (blocks3_b6_nonneg_of_ge_one hr)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (160 * r ^ 3) / (720 * r ^ 9) := by
            exact div_le_div₀ (by positivity) (blocks3_b6_le hr) (by positivity)
              (by nlinarith [hb3_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 7 by positivity]
  calc
    ‖((blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖
        = ‖(blocks3SaddleB6Real r : ℂ) /
            (720 * (blocks3SaddleBReal r : ℂ) ^ 3)‖ * |x| ^ 6 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 6 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 6)
    _ = 10 * |x| ^ 6 / r ^ 4 := by ring

private lemma blocks3_third_extra7_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * (((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
        (blocks3SaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖ ≤
        10 * |x| ^ 7 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hden_ge := blocks3_sqrtB_pow_three_mul_b_pow_two_ge_r_pow_ten hr
  have hnum_nonneg : 0 ≤ blocks3SaddleB3Real r * blocks3SaddleB4Real r :=
    mul_nonneg (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b4_nonneg_of_ge_one hr)
  have hnum_le : blocks3SaddleB3Real r * blocks3SaddleB4Real r ≤ 250 * r ^ 6 := by
    calc
      blocks3SaddleB3Real r * blocks3SaddleB4Real r
          ≤ (10 * r ^ 3) * (25 * r ^ 3) :=
            mul_le_mul (blocks3_b3_le hr) (blocks3_b4_le hr)
              (blocks3_b4_nonneg_of_ge_one hr) (by positivity)
      _ = 250 * r ^ 6 := by ring
  have hcoef :
      ‖(((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
          (blocks3SaddleBReal r : ℂ) ^ 2))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖(((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
          (blocks3SaddleBReal r : ℂ) ^ 2))‖
          =
            (blocks3SaddleB3Real r * blocks3SaddleB4Real r) /
              (144 * (Real.sqrt (blocks3SaddleBReal r)) ^ 3 *
                (blocks3SaddleBReal r) ^ 2) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_sqrtB_norm_eq_of_ge_one hr, blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (250 * r ^ 6) / (144 * r ^ 10) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hden_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [show 0 ≤ r ^ 10 by positivity]
  calc
    ‖Complex.I * (((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
        (blocks3SaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖
        = ‖(((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
            (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
              (blocks3SaddleBReal r : ℂ) ^ 2))‖ * |x| ^ 7 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 7 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 7)
    _ = 10 * |x| ^ 7 / r ^ 4 := by ring

private lemma blocks3_third_extra8a_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
      (720 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖ ≤
        10 * |x| ^ 8 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hnum_nonneg : 0 ≤ blocks3SaddleB3Real r * blocks3SaddleB5Real r :=
    mul_nonneg (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b5_nonneg_of_ge_one hr)
  have hnum_le : blocks3SaddleB3Real r * blocks3SaddleB5Real r ≤ 600 * r ^ 6 := by
    calc
      blocks3SaddleB3Real r * blocks3SaddleB5Real r
          ≤ (10 * r ^ 3) * (60 * r ^ 3) :=
            mul_le_mul (blocks3_b3_le hr) (blocks3_b5_le hr)
              (blocks3_b5_nonneg_of_ge_one hr) (by positivity)
      _ = 600 * r ^ 6 := by ring
  have hcoef :
      ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
        (720 * (blocks3SaddleBReal r : ℂ) ^ 4))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
        (720 * (blocks3SaddleBReal r : ℂ) ^ 4))‖
          = (blocks3SaddleB3Real r * blocks3SaddleB5Real r) /
              (720 * (blocks3SaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (600 * r ^ 6) / (720 * r ^ 12) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 10 by positivity]
  calc
    ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
      (720 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖
        = ‖(((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
            (720 * (blocks3SaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ = 10 * |x| ^ 8 / r ^ 4 := by ring

private lemma blocks3_third_extra8b_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖ ≤
        10 * |x| ^ 8 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb4_ge := blocks3_b_pow_four_ge_r_pow_twelve hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hnum_le : (blocks3SaddleB4Real r) ^ 2 ≤ 625 * r ^ 6 := by
    calc
      (blocks3SaddleB4Real r) ^ 2 ≤ (25 * r ^ 3) ^ 2 :=
        pow_le_pow_left₀ (blocks3_b4_nonneg_of_ge_one hr) (blocks3_b4_le hr) 2
      _ = 625 * r ^ 6 := by ring
  have hcoef :
      ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (blocks3SaddleBReal r : ℂ) ^ 4))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (blocks3SaddleBReal r : ℂ) ^ 4))‖
          = (blocks3SaddleB4Real r) ^ 2 / (1152 * (blocks3SaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sq_nonneg _)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (625 * r ^ 6) / (1152 * r ^ 12) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 10 by positivity]
  calc
    ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖
        = ‖((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
            (1152 * (blocks3SaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ = 10 * |x| ^ 8 / r ^ 4 := by ring

private lemma blocks3_third_extra9_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖ ≤
        10 * |x| ^ 9 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsqrt9_ge := blocks3_sqrtB_pow_nine_ge_r_pow_thirteen hr
  have hnum_le : (blocks3SaddleB3Real r) ^ 3 ≤ 1000 * r ^ 9 := by
    calc
      (blocks3SaddleB3Real r) ^ 3 ≤ (10 * r ^ 3) ^ 3 :=
        pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 3
      _ = 1000 * r ^ 9 := by ring
  have hcoef :
      ‖((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9))‖
          = (blocks3SaddleB3Real r) ^ 3 /
              (1296 * (Real.sqrt (blocks3SaddleBReal r)) ^ 9) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (blocks3_b3_nonneg_of_ge_one hr) 3)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_sqrtB_norm_eq_of_ge_one hr]
      _ ≤ (1000 * r ^ 9) / (1296 * r ^ 13) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hsqrt9_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [show 0 ≤ r ^ 13 by positivity]
  calc
    ‖Complex.I * ((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖
        = ‖((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
            (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9))‖ * |x| ^ 9 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 9 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 9)
    _ = 10 * |x| ^ 9 / r ^ 4 := by ring

private lemma blocks3_third_extra10_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖ ≤
        10 * |x| ^ 10 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb5_ge := blocks3_b_pow_five_ge_r_pow_fifteen hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hb3sq : (blocks3SaddleB3Real r) ^ 2 ≤ (10 * r ^ 3) ^ 2 :=
    pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 2
  have hnum_nonneg : 0 ≤ (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r :=
    mul_nonneg (sq_nonneg _) (blocks3_b4_nonneg_of_ge_one hr)
  have hnum_le :
      (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r ≤ 2500 * r ^ 9 := by
    calc
      (blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r
          ≤ (10 * r ^ 3) ^ 2 * (25 * r ^ 3) :=
            mul_le_mul hb3sq (blocks3_b4_le hr)
              (blocks3_b4_nonneg_of_ge_one hr) (by positivity)
      _ = 2500 * r ^ 9 := by ring
  have hcoef :
      ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
        (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
        (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)))‖
          = ((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r) /
              (1728 * (blocks3SaddleBReal r) ^ 5) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (2500 * r ^ 9) / (1728 * r ^ 15) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb5_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 13 by positivity]
  calc
    ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖
        = ‖(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
            (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)))‖ * |x| ^ 10 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 10 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 10)
    _ = 10 * |x| ^ 10 / r ^ 4 := by ring

private lemma blocks3_third_extra12_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (blocks3SaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12‖ ≤
        10 * |x| ^ 12 / r ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb6_ge := blocks3_b_pow_six_ge_r_pow_eighteen hr
  have h1_le_r2 := blocks3_one_le_r_sq hr
  have hnum_le : (blocks3SaddleB3Real r) ^ 4 ≤ 10000 * r ^ 12 := by
    calc
      (blocks3SaddleB3Real r) ^ 4 ≤ (10 * r ^ 3) ^ 4 :=
        pow_le_pow_left₀ (blocks3_b3_nonneg_of_ge_one hr) (blocks3_b3_le hr) 4
      _ = 10000 * r ^ 12 := by ring
  have hcoef :
      ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (blocks3SaddleBReal r : ℂ) ^ 6))‖ ≤ 10 / r ^ 4 := by
    calc
      ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (blocks3SaddleBReal r : ℂ) ^ 6))‖
          = (blocks3SaddleB3Real r) ^ 4 / (31104 * (blocks3SaddleBReal r) ^ 6) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (blocks3_b3_nonneg_of_ge_one hr) 4)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [blocks3_b_norm_eq_of_ge_one hr]
      _ ≤ (10000 * r ^ 12) / (31104 * r ^ 18) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb6_ge])
      _ ≤ 10 / r ^ 4 := by
            field_simp [hrpos.ne']
            nlinarith [h1_le_r2, show 0 ≤ r ^ 16 by positivity]
  calc
    ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (blocks3SaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12‖
        = ‖((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
            (31104 * (blocks3SaddleBReal r : ℂ) ^ 6))‖ * |x| ^ 12 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 / r ^ 4) * |x| ^ 12 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 12)
    _ = 10 * |x| ^ 12 / r ^ 4 := by ring

private lemma norm_add8_le (z1 z2 z3 z4 z5 z6 z7 z8 : ℂ) :
    ‖z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ + ‖z6‖ + ‖z7‖ + ‖z8‖ := by
  have h1 : ‖z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z1‖ + ‖z2 + z3 + z4 + z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z1 (z2 + z3 + z4 + z5 + z6 + z7 + z8)
  have h2 : ‖z2 + z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z2‖ + ‖z3 + z4 + z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z2 (z3 + z4 + z5 + z6 + z7 + z8)
  have h3 : ‖z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z3‖ + ‖z4 + z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z3 (z4 + z5 + z6 + z7 + z8)
  have h4 : ‖z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z4‖ + ‖z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z4 (z5 + z6 + z7 + z8)
  have h5 : ‖z5 + z6 + z7 + z8‖ ≤ ‖z5‖ + ‖z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z5 (z6 + z7 + z8)
  have h6 : ‖z6 + z7 + z8‖ ≤ ‖z6‖ + ‖z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z6 (z7 + z8)
  have h7 : ‖z7 + z8‖ ≤ ‖z7‖ + ‖z8‖ := norm_add_le z7 z8
  nlinarith

private lemma blocks3_third_extra_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
        blocks3SaddleB5Real blocks3SaddleB6Real r x -
      saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x‖
      ≤ 1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
        |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 4 := by
  let T5 : ℂ :=
    Complex.I * ((blocks3SaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5
  let T6 : ℂ :=
    -((blocks3SaddleB6Real r : ℂ) / (720 * (blocks3SaddleBReal r : ℂ) ^ 3)) *
      (x : ℂ) ^ 6
  let T7 : ℂ :=
    -Complex.I * (((blocks3SaddleB3Real r * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 3 *
        (blocks3SaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7
  let T8a : ℂ :=
    (((blocks3SaddleB3Real r * blocks3SaddleB5Real r : ℝ) : ℂ) /
      (720 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T8b : ℂ :=
    ((((blocks3SaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (blocks3SaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T9 : ℂ :=
    Complex.I * ((((blocks3SaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (blocks3SaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9
  let T10 : ℂ :=
    -(((((blocks3SaddleB3Real r) ^ 2 * blocks3SaddleB4Real r : ℝ) : ℂ) /
      (1728 * (blocks3SaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)
  let T12 : ℂ :=
    ((((blocks3SaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (blocks3SaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12
  have h5 : ‖T5‖ ≤ 10 * |x| ^ 5 / r ^ 4 := by
    dsimp [T5]
    exact blocks3_third_extra5_norm_le (r := r) (x := x) hr
  have h6 : ‖T6‖ ≤ 10 * |x| ^ 6 / r ^ 4 := by
    dsimp [T6]
    simpa using blocks3_third_extra6_norm_le (r := r) (x := x) hr
  have h7 : ‖T7‖ ≤ 10 * |x| ^ 7 / r ^ 4 := by
    dsimp [T7]
    simpa [norm_neg] using blocks3_third_extra7_norm_le (r := r) (x := x) hr
  have h8a : ‖T8a‖ ≤ 10 * |x| ^ 8 / r ^ 4 := by
    dsimp [T8a]
    exact blocks3_third_extra8a_norm_le (r := r) (x := x) hr
  have h8b : ‖T8b‖ ≤ 10 * |x| ^ 8 / r ^ 4 := by
    dsimp [T8b]
    exact blocks3_third_extra8b_norm_le (r := r) (x := x) hr
  have h9 : ‖T9‖ ≤ 10 * |x| ^ 9 / r ^ 4 := by
    dsimp [T9]
    exact blocks3_third_extra9_norm_le (r := r) (x := x) hr
  have h10 : ‖T10‖ ≤ 10 * |x| ^ 10 / r ^ 4 := by
    dsimp [T10]
    simpa [norm_neg] using blocks3_third_extra10_norm_le (r := r) (x := x) hr
  have h12 : ‖T12‖ ≤ 10 * |x| ^ 12 / r ^ 4 := by
    dsimp [T12]
    exact blocks3_third_extra12_norm_le (r := r) (x := x) hr
  have hdiff :
      saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
          blocks3SaddleB5Real blocks3SaddleB6Real r x -
        saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x =
        T5 + T6 + T7 + T8a + T8b + T9 + T10 + T12 := by
    dsimp [T5, T6, T7, T8a, T8b, T9, T10, T12]
    ring
  have hnonneg : 0 ≤ |x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
      |x| ^ 9 + |x| ^ 10 + |x| ^ 12 := by positivity
  rw [hdiff]
  calc
    ‖T5 + T6 + T7 + T8a + T8b + T9 + T10 + T12‖
        ≤ ‖T5‖ + ‖T6‖ + ‖T7‖ + ‖T8a‖ + ‖T8b‖ + ‖T9‖ + ‖T10‖ + ‖T12‖ :=
          norm_add8_le T5 T6 T7 T8a T8b T9 T10 T12
    _ ≤ 10 * |x| ^ 5 / r ^ 4 + 10 * |x| ^ 6 / r ^ 4 +
          10 * |x| ^ 7 / r ^ 4 + 10 * |x| ^ 8 / r ^ 4 +
          10 * |x| ^ 8 / r ^ 4 + 10 * |x| ^ 9 / r ^ 4 +
          10 * |x| ^ 10 / r ^ 4 + 10 * |x| ^ 12 / r ^ 4 := by
          nlinarith
    _ ≤ 1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
          |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 4 := by
          have hr4pos : 0 < r ^ 4 := by positivity
          field_simp [hr4pos.ne']
          nlinarith [hnonneg, pow_nonneg (abs_nonneg x) 5,
            pow_nonneg (abs_nonneg x) 6, pow_nonneg (abs_nonneg x) 7,
            pow_nonneg (abs_nonneg x) 8, pow_nonneg (abs_nonneg x) 9,
            pow_nonneg (abs_nonneg x) 10, pow_nonneg (abs_nonneg x) 12]

private lemma blocks3_local_third_extra_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
              blocks3SaddleB5Real blocks3SaddleB6Real r x -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖) /
          blocks3SecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, blocks3ThirdGaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact blocks3ThirdGaussianDom_integral_nonneg
  have hupper_tendsto :
      Tendsto (fun r : ℝ => (1000 * M) / r) atTop (𝓝 0) := by
    have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv, mul_assoc] using hinv.const_mul (1000 * M)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3SecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
              blocks3SaddleB5Real blocks3SaddleB6Real r x -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3SecondCorrScale_pos_eventually] with
      r hr hcorrPos
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
          blocks3SaddleB5Real blocks3SaddleB6Real r x -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
            blocks3SaddleB4Real r x)‖
    let G : ℝ → ℝ := fun x => (1000 / r ^ 4) * blocks3ThirdGaussianDom x
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ G x := by
      intro x hx
      have hdiff := blocks3_third_extra_norm_le (r := r) (x := x) hr
      dsimp [F, G, blocks3ThirdGaussianDom]
      rw [norm_mul]
      have hgauss :
          ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
        rw [Complex.norm_exp]
        congr 1
        simp [pow_two]
      rw [hgauss]
      calc
        Real.exp (-(x ^ 2) / 2) *
            ‖saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
                blocks3SaddleB5Real blocks3SaddleB6Real r x -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x‖
            ≤ Real.exp (-(x ^ 2) / 2) *
                (1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                  |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 4) :=
              mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
        _ = 1000 / r ^ 4 *
            (Real.exp (-(x ^ 2) / 2) *
              (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                |x| ^ 9 + |x| ^ 10 + |x| ^ 12)) := by ring
    have hFint : IntervalIntegrable F volume (-L) L := by
      have hcont : Continuous F := by
        dsimp [F]
        simp only [saddleThirdPoly, saddleSecondPoly, blocks3SaddleBReal,
          blocks3SaddleB3Real, blocks3SaddleB4Real, blocks3SaddleB5Real,
          blocks3SaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hGint : IntervalIntegrable G volume (-L) L := by
      exact (blocks3ThirdGaussianDom_continuous.const_mul (1000 / r ^ 4)).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤ (1000 / r ^ 4) * M := by
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, G x :=
          intervalIntegral.integral_mono_on hle hFint hGint hpoint
        _ = (1000 / r ^ 4) * (∫ x in -L..L, blocks3ThirdGaussianDom x) := by
          dsimp [G]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (1000 / r ^ 4) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact blocks3ThirdGaussianDom_window_le_integral hLnonneg)
            (div_nonneg (by norm_num) (by positivity))
    have hnum_nonneg : 0 ≤ (1000 / r ^ 4) * M :=
      mul_nonneg (div_nonneg (by norm_num) (by positivity)) hM_nonneg
    have hmain :
        (∫ x in -L..L, F x) / blocks3SecondCorrScale r ≤
          ((1000 / r ^ 4) * M) / blocks3SecondCorrScale r :=
      div_le_div_of_nonneg_right hIntBound hcorrPos.le
    calc
      ((∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
              blocks3SaddleB5Real blocks3SaddleB6Real r x -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real r x)‖) /
          blocks3SecondCorrScale r)
          = (∫ x in -L..L, F x) / blocks3SecondCorrScale r := by rfl
      _ ≤ ((1000 / r ^ 4) * M) / blocks3SecondCorrScale r := hmain
      _ = (1000 * M) / r := by
        unfold blocks3SecondCorrScale
        rw [Real.rpow_neg hrpos.le]
        rw [show r ^ (3 : ℝ) = r ^ 3 by exact Real.rpow_natCast r 3]
        field_simp [hrpos.ne']

theorem blocks3_local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
          (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real
                blocks3SaddleB4Real blocks3SaddleB5Real blocks3SaddleB6Real r x)‖) /
          blocks3ThirdCorrScale r)
      atTop (𝓝 0) := by
  unfold blocks3ThirdCorrScale
  let T : ℝ → ℝ := fun r =>
    (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
      (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
            blocks3SaddleB5Real blocks3SaddleB6Real r x)‖) / blocks3SecondCorrScale r
  let S : ℝ → ℝ := fun r =>
    (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
      (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖) /
      blocks3SecondCorrScale r
  let E : ℝ → ℝ := fun r =>
    (∫ x in -(blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r))..
      (blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
          blocks3SaddleB5Real blocks3SaddleB6Real r x -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖) /
      blocks3SecondCorrScale r
  change Tendsto T atTop (𝓝 0)
  have hsecond := blocks3_local_second_L1
  have hextra := blocks3_local_third_extra_L1
  have hsum : Tendsto (fun r : ℝ => S r + E r) atTop (𝓝 0) := by
    simpa [S, E] using hsecond.add hextra
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3SecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
                blocks3SaddleB5Real blocks3SaddleB6Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    dsimp [T]
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), blocks3SecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := blocks3SaddleDeltaReal r * Real.sqrt (blocks3SaddleBReal r)
    let FT : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
            blocks3SaddleB5Real blocks3SaddleB6Real r x)‖
    let FS : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
            (x / Real.sqrt (blocks3SaddleBReal r)) -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖
    let FE : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
          blocks3SaddleB5Real blocks3SaddleB6Real r x -
          saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖
    have hLnonneg : 0 ≤ L := by
      dsimp [L, blocks3SaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, FT x ≤ FS x + FE x := by
      intro x hx
      dsimp [FT, FS, FE]
      calc
        ‖Complex.exp (-(x ^ 2) / 2) *
          (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
              (x / Real.sqrt (blocks3SaddleBReal r)) -
            saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
              blocks3SaddleB5Real blocks3SaddleB6Real r x)‖
            =
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x) -
            Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
                blocks3SaddleB5Real blocks3SaddleB6Real r x -
                saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                  blocks3SaddleB4Real r x)‖ := by
              congr 1
              ring
        _ ≤
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio blocks3Fun blocks3SaddleAReal blocks3SaddleBReal r
                (x / Real.sqrt (blocks3SaddleBReal r)) -
              saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real r x)‖ +
          ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly blocks3SaddleBReal blocks3SaddleB3Real blocks3SaddleB4Real
                blocks3SaddleB5Real blocks3SaddleB6Real r x -
                saddleSecondPoly blocks3SaddleBReal blocks3SaddleB3Real
                  blocks3SaddleB4Real r x)‖ :=
            norm_sub_le _ _
    have hFTint : IntervalIntegrable FT volume (-L) L := by
      have hcont : Continuous FT := by
        dsimp [FT]
        simp only [blocks3_saddleLocalRatio_eq]
        simp only [saddleThirdPoly, saddleSecondPoly, blocks3LocalExponent,
          ExpStirling.expLocalRemainder, blocks3Fun, blocks3SaddleAReal,
          blocks3SaddleBReal, blocks3SaddleB3Real, blocks3SaddleB4Real,
          blocks3SaddleB5Real, blocks3SaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hFSint : IntervalIntegrable FS volume (-L) L := by
      have hcont : Continuous FS := by
        dsimp [FS]
        simp only [blocks3_saddleLocalRatio_eq]
        simp only [saddleSecondPoly, blocks3LocalExponent, ExpStirling.expLocalRemainder,
          blocks3Fun, blocks3SaddleAReal, blocks3SaddleBReal, blocks3SaddleB3Real,
          blocks3SaddleB4Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hFEint : IntervalIntegrable FE volume (-L) L := by
      have hcont : Continuous FE := by
        dsimp [FE]
        simp only [saddleThirdPoly, saddleSecondPoly, blocks3SaddleBReal, blocks3SaddleB3Real,
          blocks3SaddleB4Real, blocks3SaddleB5Real, blocks3SaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hsumInt : IntervalIntegrable (fun x : ℝ => FS x + FE x) volume (-L) L :=
      hFSint.add hFEint
    have hInt :
        (∫ x in -L..L, FT x) ≤ (∫ x in -L..L, FS x) + (∫ x in -L..L, FE x) := by
      calc
        (∫ x in -L..L, FT x) ≤ ∫ x in -L..L, FS x + FE x :=
          intervalIntegral.integral_mono_on hle hFTint hsumInt hpoint
        _ = (∫ x in -L..L, FS x) + (∫ x in -L..L, FE x) := by
          rw [intervalIntegral.integral_add hFSint hFEint]
    have hdiv :
        (∫ x in -L..L, FT x) / blocks3SecondCorrScale r ≤
          ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            blocks3SecondCorrScale r :=
      div_le_div_of_nonneg_right hInt hcorr.le
    calc
      T r = (∫ x in -L..L, FT x) / blocks3SecondCorrScale r := by rfl
      _ ≤ ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            blocks3SecondCorrScale r := hdiv
      _ = S r + E r := by
        dsimp [S, E, FS, FE, L]
        ring

/-- The produced third-order H-admissible instance for blocks of size at most three. -/
def blocks3ThirdOrderHAdmissible :
    ThirdOrderHAdmissible blocks3HAdmissible blocks3SecondOrderHAdmissible where
  b5 := blocks3SaddleB5Real
  b6 := blocks3SaddleB6Real
  corrScale3 := blocks3ThirdCorrScale
  corrScale3_pos := by
    simpa [blocks3HAdmissible, blocks3ThirdCorrScale] using
      blocks3SecondCorrScale_pos_eventually
  corrScale3_tendsto_zero := by
    simpa [blocks3HAdmissible, blocks3ThirdCorrScale] using
      blocks3SecondCorrScale_tendsto_zero
  corrScale3_dominates_correction := by
    simpa [blocks3HAdmissible, blocks3SecondOrderHAdmissible, blocks3ThirdCorrScale]
      using blocks3_saddleThirdCorrectionScale_le_thirdCorrScale
  local_third_L1 := by
    simpa [blocks3HAdmissible, blocks3SecondOrderHAdmissible, blocks3ThirdCorrScale]
      using blocks3_local_third_L1
  tail_third_uniform := by
    simpa [blocks3HAdmissible, blocks3ThirdCorrScale] using blocks3_tail_second_uniform

/-- Abstract third-order saddle theorem specialized to the blocks-<=3 saddle. -/
theorem blocks3_coeff_thirdOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      blocks3Series.coeff n / blocks3SecondOrderSaddleScale n -
        (1 + (blocks3SecondCorrectionAtSaddle n : ℂ) +
          (blocks3ThirdCorrectionAtSaddle n : ℂ)))
      =o[atTop]
    (fun n : ℕ => (blocks3ThirdCorrScale (blocks3SaddleRadius n) : ℂ)) := by
  have h :=
    coeff_thirdOrder_saddle
      blocks3HAdmissible blocks3SecondOrderHAdmissible blocks3ThirdOrderHAdmissible
      blocks3HAdmissibleSaddleSequence
  simpa [blocks3SecondOrderSaddleScale, blocks3SecondCorrectionAtSaddle,
    blocks3ThirdCorrectionAtSaddle, HAdmissible.B, blocks3HAdmissible,
    blocks3HAdmissibleSaddleSequence, blocks3SecondOrderHAdmissible,
    blocks3ThirdOrderHAdmissible, blocks3ThirdCorrScale] using h

end Blocks3HAdmissible
end

open Blocks3HAdmissible
open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
theorem solution :
    (fun n : ℕ => blocks3ThirdOrderNumberError n)
      =o[atTop]
    (fun n : ℕ => (blocks3ThirdCorrScale (blocks3SaddleRadius n) : ℂ)) := by
  simpa [blocks3ThirdOrderNumberError, blocks3SecondOrderSaddleScale,
    blocks3SecondCorrectionAtSaddle, blocks3ThirdCorrectionAtSaddle,
    PowerSeries.coeff_toFMLS, blocks3Carrier_coeff, blocks3CoeffR]
    using blocks3_coeff_thirdOrder_saddle_from_HAdmissible
