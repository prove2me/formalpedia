-- Prove2me | solution 1 for FragmentedPermHAdmissible.fragPerm_count_over_factorial_thirdOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:00:40.450581+00:00
-- url     : https://prove2.me/submissions/0a9e539d-7737-4838-94ae-21fd4af43ab0

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder_x1
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Exp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bell
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
import Theorems.Thm_FragmentedPermHAdmissible_fragPerm_local_exponent_norm_le
import Theorems.Thm_FragmentedPermHAdmissible_fragPerm_local_integrand_bound
import Theorems.Thm_FragmentedPermHAdmissible_fragPerm_tail_bound_eventually
import Theorems.Thm_FragmentedPermHAdmissible_fragPerm_third_local_integrand_bound
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
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
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
open Filter
open scoped PowerSeries Topology

noncomputable section

namespace PowerSeries

lemma coeff_pole1 (n : ℕ) : coeff (R := ℂ) n pole1 = 1 := by
  simp [pole1]

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
# Fragmented permutations: finite-radius H-admissible saddle data

Fragmented permutations are the labelled class `SET(SEQ_{\ge 1}(Z))`, with EGF
`exp (z / (1 - z))`.  This file packages the finite-radius Hayman data for the
committed `HAdmissible` bridge.  The saddle regime is `r -> 1-`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace FragmentedPermHAdmissible

lemma fragPermInnerPS_constantCoeff :
    PowerSeries.constantCoeff fragPermInnerPS = 0 := by
  simp [fragPermInnerPS]

lemma pole1_toFMLS_eq_geometric :
    PowerSeries.toFMLS PowerSeries.pole1 = formalMultilinearSeries_geometric ℂ ℂ := by
  ext n
  simp [PowerSeries.toFMLS, PowerSeries.coeff_pole1, formalMultilinearSeries_geometric]

lemma fragPermInner_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => z / (1 - z))
      (PowerSeries.toFMLS fragPermInnerPS) (0 : ℂ) := by
  have hX : HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) :=
    InvolutionHAdmissible.hasFPowerSeriesAt_id_toFMLS_X
  have hpole : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (PowerSeries.toFMLS PowerSeries.pole1) (0 : ℂ) := by
    simpa [pole1_toFMLS_eq_geometric] using
      (hasFPowerSeriesOnBall_inv_one_sub ℂ ℂ).hasFPowerSeriesAt
  have hmul := InvolutionHAdmissible.hasFPowerSeriesAt_mul_toFMLS hX hpole
  simpa [fragPermInnerPS, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma fragPermFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt fragPermFun fragPermSeries (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp
      (PowerSeries.toFMLS (PowerSeries.exp ℂ)) ((fun z : ℂ => z / (1 - z)) 0) := by
    simpa [expCarrier] using ExpStirling.expCarrier_hasFPowerSeriesAt_zero
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => z / (1 - z)) houter fragPermInner_hasFPowerSeriesAt_zero
  change HasFPowerSeriesAt fragPermFun (PowerSeries.toFMLS fragPermCarrier) (0 : ℂ)
  rw [fragPermCarrier]
  rw [PowerSeries.toFMLS_subst_eq_comp fragPermInnerPS_constantCoeff]
  simpa [Function.comp_def, fragPermFun, fragPermSeries] using hcomp

lemma fragPermRadFilter_neBot : fragPermRadFilter.NeBot := by
  unfold fragPermRadFilter
  infer_instance

lemma fragPerm_eventually_Ioo_zero_one :
    ∀ᶠ r : ℝ in fragPermRadFilter, r ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [fragPermRadFilter, eventually_nhdsWithin_iff]
  filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2)] with r hr hleft
  exact ⟨hr.1, hleft⟩

lemma fragPerm_eventually_Ioo_half_one :
    ∀ᶠ r : ℝ in fragPermRadFilter, r ∈ Set.Ioo ((1 : ℝ) / 2) 1 := by
  rw [fragPermRadFilter, eventually_nhdsWithin_iff]
  filter_upwards [Ioo_mem_nhds (by norm_num : ((1 : ℝ) / 2) < 1)
      (by norm_num : (1 : ℝ) < 2)] with r hr hleft
  exact ⟨hr.1, hleft⟩

lemma fragPerm_r_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  exact hr.1

lemma fragPerm_differentiableOn_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      DifferentiableOn ℂ fragPermFun (Metric.closedBall (0 : ℂ) r) := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr z hz
  have hnorm_le : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hzne : (1 : ℂ) - z ≠ 0 := by
    intro hzero
    have hz_eq : z = 1 := by
      exact sub_eq_zero.mp hzero |>.symm
    have hnorm_one : ‖z‖ = 1 := by simp [hz_eq]
    have : (1 : ℝ) ≤ r := by simpa [hnorm_one] using hnorm_le
    linarith [hr.2]
  unfold fragPermFun
  have hnum : DifferentiableAt ℂ (fun z : ℂ => z) z := differentiableAt_id
  have hden : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - z) z :=
    (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
  have hquot : DifferentiableAt ℂ (fun z : ℂ => z / (1 - z)) z :=
    hnum.div hden hzne
  exact (Complex.differentiable_exp.differentiableAt.comp z hquot).differentiableWithinAt

lemma fragPerm_f_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < (fragPermFun (r : ℂ)).re := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermFun
  have harg : (r : ℂ) / (1 - (r : ℂ)) = ((r / (1 - r) : ℝ) : ℂ) := by
    norm_num
  rw [harg]
  rw [← Complex.ofReal_exp]
  exact Real.exp_pos _

lemma fragPerm_b_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < fragPermSaddleBReal r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermSaddleBReal
  have hrpos : 0 < r := hr.1
  have hden : 0 < (1 - r) ^ 3 := by
    have hbase : 0 < 1 - r := by linarith [hr.2]
    positivity
  have hnum : 0 < r * (1 + r) := by positivity
  exact div_pos hnum hden

lemma fragPerm_delta_le_one_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, fragPermSaddleDeltaReal r ≤ 1 := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hbase_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
  have hbase_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  unfold fragPermSaddleDeltaReal
  exact Real.rpow_le_one hbase_nonneg hbase_le_one
    (by norm_num : (0 : ℝ) ≤ 7 / 5)

lemma fragPerm_one_sub_tendsto_nhdsGT_zero :
    Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) := by
  unfold fragPermRadFilter
  have hr : Tendsto (fun r : ℝ => r) (𝓝[Set.Iio (1 : ℝ)] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [id] using
      (tendsto_id.mono_right
        (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Iio (1 : ℝ))))
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[Set.Iio (1 : ℝ)] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hnhds : Tendsto (fun r : ℝ => 1 - r)
      (𝓝[Set.Iio (1 : ℝ)] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (hc.sub hr)
  have hpos : ∀ᶠ r : ℝ in 𝓝[Set.Iio (1 : ℝ)] (1 : ℝ),
      1 - r ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hrlt
    exact sub_pos.mpr (by simpa using hrlt)
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (fun r : ℝ => 1 - r) hnhds hpos

lemma fragPerm_one_sub_rpow_neg_tendsto_atTop :
    Tendsto (fun r : ℝ => (1 - r) ^ (-(1 / 10 : ℝ))) fragPermRadFilter atTop := by
  have hinv : Tendsto (fun r : ℝ => (1 - r)⁻¹) fragPermRadFilter atTop :=
    tendsto_inv_nhdsGT_zero.comp fragPerm_one_sub_tendsto_nhdsGT_zero
  have hpow : Tendsto (fun r : ℝ => ((1 - r)⁻¹) ^ (1 / 10 : ℝ))
      fragPermRadFilter atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hinv
  refine Tendsto.congr' ?_ hpow
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hnonneg : 0 ≤ 1 - r := by linarith [hr.2]
  rw [Real.inv_rpow hnonneg]
  rw [← Real.rpow_neg hnonneg]

lemma fragPerm_sqrt_b_lower_of_Ioo_half_one {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ)) ≤
      Real.sqrt (fragPermSaddleBReal r) := by
  let u : ℝ := 1 - r
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hden_pos : 0 < u ^ 3 := by positivity
  have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
  have hb_lower : (1 / 2 : ℝ) / u ^ 3 ≤ fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u] at hden_pos ⊢
    exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
  have hx_sq : ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) ^ 2 ≤
      fragPermSaddleBReal r := by
    calc
      ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) ^ 2
          = (1 / 4 : ℝ) * u ^ (-(3 : ℝ)) := by
            rw [mul_pow]
            norm_num
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
      _ ≤ (1 / 2 : ℝ) * u ^ (-(3 : ℝ)) := by
            have hpow_nonneg : 0 ≤ u ^ (-(3 : ℝ)) := Real.rpow_nonneg hu_nonneg _
            nlinarith
      _ = (1 / 2 : ℝ) / u ^ 3 := by
            rw [Real.rpow_neg hu_nonneg]
            have hu3 : u ^ (3 : ℝ) = u ^ 3 := by
              norm_num [Real.rpow_natCast]
            rw [hu3]
            ring
      _ ≤ fragPermSaddleBReal r := hb_lower
  have hsqrt := Real.le_sqrt_of_sq_le hx_sq
  simpa [u] using hsqrt

lemma fragPerm_one_sub_rpow_neg_one_fifth_tendsto_atTop :
    Tendsto (fun r : ℝ => (1 - r) ^ (-(1 / 5 : ℝ))) fragPermRadFilter atTop := by
  have hinv : Tendsto (fun r : ℝ => (1 - r)⁻¹) fragPermRadFilter atTop :=
    tendsto_inv_nhdsGT_zero.comp fragPerm_one_sub_tendsto_nhdsGT_zero
  have hpow : Tendsto (fun r : ℝ => ((1 - r)⁻¹) ^ (1 / 5 : ℝ))
      fragPermRadFilter atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hinv
  refine Tendsto.congr' ?_ hpow
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hnonneg : 0 ≤ 1 - r := by linarith [hr.2]
  rw [Real.inv_rpow hnonneg]
  rw [← Real.rpow_neg hnonneg]

lemma fragPermTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 ≤ fragPermTailE r :=
  Eventually.of_forall fun _ => by
    unfold fragPermTailE
    positivity

lemma fragPermTailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) *
      fragPermTailE r) fragPermRadFilter (𝓝 0) := by
  let c : ℝ := fragPermTailC
  have hc : 0 < c := by
    dsimp [c, fragPermTailC]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (15 / 2 : ℝ) * Real.exp (-c * y))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (15 / 2 : ℝ) c hc
  have hy := fragPerm_one_sub_rpow_neg_one_fifth_tendsto_atTop
  have hcomp :
      Tendsto
        (fun r : ℝ => ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (15 / 2 : ℝ) *
          Real.exp (-c * ((1 - r) ^ (-(1 / 5 : ℝ)))))
        fragPermRadFilter (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto
        (fun r : ℝ => Real.sqrt (4 * Real.pi) *
          (((1 - r) ^ (-(1 / 5 : ℝ))) ^ (15 / 2 : ℝ) *
            Real.exp (-c * ((1 - r) ^ (-(1 / 5 : ℝ))))))
        fragPermRadFilter (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (4 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · exact Eventually.of_forall fun r => by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
    let u : ℝ := 1 - r
    have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have hnum_le : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hr.2]
    have hB_le : fragPermSaddleBReal r ≤ 2 / u ^ 3 := by
      unfold fragPermSaddleBReal
      dsimp [u]
      have hden_pos : 0 < (1 - r) ^ 3 := by positivity
      exact div_le_div_of_nonneg_right hnum_le hden_pos.le
    have hmul : 2 * Real.pi * fragPermSaddleBReal r ≤ 4 * Real.pi / u ^ 3 := by
      calc
        2 * Real.pi * fragPermSaddleBReal r
            ≤ 2 * Real.pi * (2 / u ^ 3) :=
              mul_le_mul_of_nonneg_left hB_le (by positivity)
        _ = 4 * Real.pi / u ^ 3 := by ring
    have hsqrt :
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) ≤
          Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
      calc
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r)
            ≤ Real.sqrt (4 * Real.pi / u ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
          have h4pi : 0 ≤ 4 * Real.pi := by positivity
          rw [div_eq_mul_inv]
          rw [Real.sqrt_mul h4pi]
          have hsqrt_inv_u3 : Real.sqrt ((u ^ 3)⁻¹) = u ^ (-(3 / 2 : ℝ)) := by
            have hinv_u3 : (u ^ 3)⁻¹ = u ^ (-3 : ℝ) := by
              rw [show u ^ 3 = u ^ (3 : ℝ) by exact (Real.rpow_natCast u 3).symm]
              rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
            rw [hinv_u3]
            rw [Real.sqrt_eq_rpow]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
          congr 1
    have hy_pow :
        ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (15 / 2 : ℝ) =
          u ^ (-(3 / 2 : ℝ)) := by
      have h :
          ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (15 / 2 : ℝ) =
            (1 - r) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_mul (by linarith : 0 ≤ 1 - r)]
        norm_num
      simpa [u] using h
    unfold fragPermTailE
    dsimp [c, fragPermTailC]
    rw [hy_pow]
    calc
      Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) *
          Real.exp (-(1 / (4 * Real.pi ^ 2)) *
            (1 - r) ^ (-(1 / 5 : ℝ)))
          ≤ (Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ))) *
              Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                (1 - r) ^ (-(1 / 5 : ℝ))) :=
            mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le
      _ = Real.sqrt (4 * Real.pi) *
            (u ^ (-(3 / 2 : ℝ)) *
              Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                (1 - r) ^ (-(1 / 5 : ℝ)))) := by ring

lemma fragPerm_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in fragPermRadFilter, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r)
        fragPermRadFilter (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
        fragPermSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt fragPermFun r n θ‖ ≤ E r) := by
  exact ⟨fragPermTailE, fragPermTailE_nonneg_eventually, fragPermTailE_decay,
    fragPerm_tail_bound_eventually⟩

lemma fragPerm_differentiableOn_closedBall_of_radius_lt_one {R : ℝ≥0}
    (hR : (R : ℝ≥0∞) < (1 : ℝ≥0∞)) :
    DifferentiableOn ℂ fragPermFun (Metric.closedBall (0 : ℂ) R) := by
  intro z hz
  have hRlt : (R : ℝ) < 1 := by
    exact ENNReal.coe_lt_one_iff.mp hR
  have hnorm_le : ‖z‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hzne : (1 : ℂ) - z ≠ 0 := by
    intro hzero
    have hz_eq : z = 1 := by
      exact sub_eq_zero.mp hzero |>.symm
    have hnorm_one : ‖z‖ = 1 := by simp [hz_eq]
    have : (1 : ℝ) ≤ R := by simpa [hnorm_one] using hnorm_le
    linarith
  unfold fragPermFun
  have hnum : DifferentiableAt ℂ (fun z : ℂ => z) z := differentiableAt_id
  have hden : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - z) z :=
    (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
  have hquot : DifferentiableAt ℂ (fun z : ℂ => z / (1 - z)) z :=
    hnum.div hden hzne
  exact (Complex.differentiable_exp.differentiableAt.comp z hquot).differentiableWithinAt

lemma fragPermSeries_one_le_radius :
    (1 : ℝ≥0∞) ≤ fragPermSeries.radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun R hRlt => ?_
  rcases eq_or_lt_of_le (zero_le R) with rfl | hRpos
  · exact zero_le _
  rcases fragPermFun_hasFPowerSeriesAt_zero with ⟨r0, hbase⟩
  have hdiff := fragPerm_differentiableOn_closedBall_of_radius_lt_one hRlt
  have hcauchy := hdiff.hasFPowerSeriesOnBall hRpos
  exact (hbase.exchange_radius hcauchy).r_le

lemma fragPerm_hasFPowerSeriesOnBall_one :
    HasFPowerSeriesOnBall fragPermFun fragPermSeries (0 : ℂ) (1 : ℝ≥0∞) := by
  refine ⟨fragPermSeries_one_le_radius, by norm_num, ?_⟩
  intro y hy
  rw [mem_eball_zero_iff] at hy
  obtain ⟨R, hyR, hRone⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hy
  rcases eq_or_lt_of_le (zero_le R) with rfl | hRpos
  · simp at hyR
  rcases fragPermFun_hasFPowerSeriesAt_zero with ⟨r0, hbase⟩
  have hdiff := fragPerm_differentiableOn_closedBall_of_radius_lt_one hRone
  have hcauchy := hdiff.hasFPowerSeriesOnBall hRpos
  exact (hbase.exchange_radius hcauchy).hasSum (mem_eball_zero_iff.mpr hyR)

lemma fragPermFun_norm_tendsto_atTop :
    Tendsto (fun r : ℝ => ‖fragPermFun (r : ℂ)‖) fragPermRadFilter atTop := by
  have hinv : Tendsto (fun r : ℝ => (1 - r)⁻¹) fragPermRadFilter atTop :=
    tendsto_inv_nhdsGT_zero.comp fragPerm_one_sub_tendsto_nhdsGT_zero
  have hhalf_inv :
      Tendsto (fun r : ℝ => (1 / 2 : ℝ) * (1 - r)⁻¹) fragPermRadFilter atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hinv
  have hquot : Tendsto (fun r : ℝ => r / (1 - r)) fragPermRadFilter atTop := by
    refine tendsto_atTop_mono' fragPermRadFilter ?_ hhalf_inv
    filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
    have hinv_nonneg : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith [hr.2] : 0 ≤ 1 - r)
    calc
      (1 / 2 : ℝ) * (1 - r)⁻¹ ≤ r * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_right hr.1.le hinv_nonneg
      _ = r / (1 - r) := by rw [div_eq_mul_inv]
  refine Tendsto.congr' ?_ (Real.tendsto_exp_atTop.comp hquot)
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermFun
  have harg : (r : ℂ) / (1 - (r : ℂ)) = ((r / (1 - r) : ℝ) : ℂ) := by
    norm_num
  rw [Complex.norm_exp]
  exact congrArg Real.exp (congrArg Complex.re harg).symm

lemma fragPermSeries_radius_le_one :
    fragPermSeries.radius ≤ (1 : ℝ≥0∞) := by
  by_contra hnot
  have hgt : (1 : ℝ≥0∞) < fragPermSeries.radius := lt_of_not_ge hnot
  have hpos : 0 < fragPermSeries.radius :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) fragPermSeries_one_le_radius
  have hpball : HasFPowerSeriesOnBall fragPermSeries.sum fragPermSeries (0 : ℂ)
      fragPermSeries.radius :=
    FormalMultilinearSeries.hasFPowerSeriesOnBall fragPermSeries hpos
  have hmem_one : (1 : ℂ) ∈ Metric.eball (0 : ℂ) fragPermSeries.radius := by
    simpa [mem_eball_zero_iff] using hgt
  have hcont :
      ContinuousAt fragPermSeries.sum (1 : ℂ) :=
    (hpball.analyticAt_of_mem hmem_one).continuousAt
  have hreal_to_one : Tendsto (fun r : ℝ => r) fragPermRadFilter (𝓝 (1 : ℝ)) := by
    unfold fragPermRadFilter
    exact tendsto_id.mono_right (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Iio (1 : ℝ)))
  have hcomplex_to_one : Tendsto (fun r : ℝ => (r : ℂ)) fragPermRadFilter (𝓝 (1 : ℂ)) := by
    exact Filter.tendsto_ofReal_iff.mpr hreal_to_one
  have hfinite :
      Tendsto (fun r : ℝ => ‖fragPermSeries.sum (r : ℂ)‖) fragPermRadFilter
        (𝓝 ‖fragPermSeries.sum (1 : ℂ)‖) := by
    have hnorm_cont : ContinuousAt (fun z : ℂ => ‖fragPermSeries.sum z‖) (1 : ℂ) :=
      hcont.norm
    exact hnorm_cont.tendsto.comp hcomplex_to_one
  have heq :
      (fun r : ℝ => ‖fragPermSeries.sum (r : ℂ)‖) =ᶠ[fragPermRadFilter]
        fun r : ℝ => ‖fragPermFun (r : ℂ)‖ := by
    filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
    have hy : (r : ℂ) ∈ Metric.eball (0 : ℂ) (1 : ℝ≥0∞) := by
      rw [mem_eball_zero_iff]
      rw [← ENNReal.coe_one]
      exact ENNReal.coe_lt_coe.2 (by
        apply NNReal.coe_lt_coe.mp
        simpa [NNReal.coe_one, coe_nnnorm, abs_of_nonneg hr.1.le] using hr.2)
    have hsum := fragPerm_hasFPowerSeriesOnBall_one.sum hy
    rw [← hsum]
    simp
  have hatTop :
      Tendsto (fun r : ℝ => ‖fragPermSeries.sum (r : ℂ)‖) fragPermRadFilter atTop :=
    Tendsto.congr' heq.symm fragPermFun_norm_tendsto_atTop
  haveI : fragPermRadFilter.NeBot := fragPermRadFilter_neBot
  exact (not_tendsto_atTop_of_tendsto_nhds hfinite) hatTop

lemma fragPermSeries_radius_eq_one_proved :
    fragPermSeries.radius = (1 : ℝ≥0∞) :=
  le_antisymm fragPermSeries_radius_le_one fragPermSeries_one_le_radius

lemma fragPerm_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ =
      Complex.exp (fragPermLocalExponent r θ) := by
  unfold saddleLocalRatio fragPermFun fragPermLocalExponent
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  ring

lemma fragPerm_delta_le_one_sub_quarter_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      fragPermSaddleDeltaReal r ≤ (1 - r) / 4 := by
  have hnhds : Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
    fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  have hpow :
      Tendsto (fun r : ℝ => (1 - r) ^ (2 / 5 : ℝ)) fragPermRadFilter (𝓝 0) := by
    simpa using hnhds.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 5))
  have hsmall :
      ∀ᶠ r : ℝ in fragPermRadFilter,
        (1 - r) ^ (2 / 5 : ℝ) ≤ (1 / 4 : ℝ) :=
    hpow.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [fragPerm_eventually_Ioo_zero_one, hsmall] with r hr hsmallr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  calc
    fragPermSaddleDeltaReal r = (1 - r) ^ (1 : ℝ) * (1 - r) ^ (2 / 5 : ℝ) := by
      unfold fragPermSaddleDeltaReal
      rw [← Real.rpow_add hu_pos]
      norm_num
    _ ≤ (1 - r) * (1 / 4 : ℝ) :=
      by
        rw [Real.rpow_one]
        exact mul_le_mul_of_nonneg_left hsmallr hu_nonneg
    _ = (1 - r) / 4 := by ring

def fragPermLocalControl (r : ℝ) : ℝ :=
  (1 - r) ^ (1 / 5 : ℝ)

lemma fragPermLocalControl_tendsto_zero :
    Tendsto fragPermLocalControl fragPermRadFilter (𝓝 0) := by
  have hnhds : Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
    fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  change Tendsto (fun r : ℝ => (1 - r) ^ (1 / 5 : ℝ)) fragPermRadFilter (𝓝 0)
  have h := hnhds.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 5))
  simpa using h

lemma fragPerm_local_scale_eq_control_eventually :
    (fun r : ℝ => (fragPermSaddleDeltaReal r) ^ 3 / (1 - r) ^ 4)
      =ᶠ[fragPermRadFilter] fragPermLocalControl := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  unfold fragPermSaddleDeltaReal fragPermLocalControl
  rw [← Real.rpow_mul_natCast hu_nonneg (7 / 5 : ℝ) 3]
  norm_num
  have hpow4 : (1 - r) ^ 4 = (1 - r) ^ (4 : ℝ) :=
    (Real.rpow_natCast (1 - r) 4).symm
  rw [hpow4]
  rw [div_eq_mul_inv, ← Real.rpow_neg hu_nonneg (4 : ℝ), ← Real.rpow_add hu_pos]
  norm_num

lemma fragPermLocalBound_tendsto_zero :
    Tendsto (fun r : ℝ =>
      fragPermLocalConstant * ((fragPermSaddleDeltaReal r) ^ 3 / (1 - r) ^ 4))
      fragPermRadFilter (𝓝 0) := by
  have hscale :
    Tendsto (fun r : ℝ => (fragPermSaddleDeltaReal r) ^ 3 / (1 - r) ^ 4)
        fragPermRadFilter (𝓝 0) :=
    Tendsto.congr' fragPerm_local_scale_eq_control_eventually.symm
      fragPermLocalControl_tendsto_zero
  simpa using hscale.const_mul fragPermLocalConstant

lemma fragPerm_local_uniform_proved :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ θ : ℝ,
      |θ| ≤ fragPermSaddleDeltaReal r →
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in fragPermRadFilter,
        fragPermLocalConstant *
          (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4) ≤ ε / 2 :=
    fragPermLocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in fragPermRadFilter,
        fragPermLocalConstant *
          (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4) ≤ 1 :=
    fragPermLocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [fragPerm_eventually_Ioo_zero_one, fragPerm_delta_le_one_eventually,
    fragPerm_delta_le_one_sub_quarter_eventually, hsmall, hone] with
      r hr hδ_one hδ_u hsmallr honer θ hθ
  rw [fragPerm_saddleLocalRatio_eq]
  have hz :
      ‖fragPermLocalExponent r θ‖ ≤
        fragPermLocalConstant *
          (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4) :=
    fragPerm_local_exponent_norm_le hr.1.le hr.2 hδ_one hδ_u hθ
  have hz_one : ‖fragPermLocalExponent r θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp (fragPermLocalExponent r θ) - 1‖
        ≤ 2 * ‖fragPermLocalExponent r θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 *
        (fragPermLocalConstant *
          (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4)) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

/-- Radius and local uniform estimates for `exp (z/(1-z))`. -/
lemma fragPerm_radius_and_local_uniform_gap :
    fragPermSeries.radius = (1 : ℝ≥0∞) ∧
    (∀ ε > 0, ∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ θ : ℝ,
      |θ| ≤ fragPermSaddleDeltaReal r →
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ ε) := by
  exact ⟨fragPermSeries_radius_eq_one_proved, fragPerm_local_uniform_proved⟩

lemma fragPermSeries_radius_eq_one :
    fragPermSeries.radius = (1 : ℝ≥0∞) :=
  fragPerm_radius_and_local_uniform_gap.1

lemma fragPerm_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ θ : ℝ,
      |θ| ≤ fragPermSaddleDeltaReal r →
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ ε :=
  fragPerm_radius_and_local_uniform_gap.2

/-- The finite-radius Hayman local and tail estimates for `exp (z/(1-z))`. -/
lemma fragPerm_hayman_uniform_estimates :
    (∀ ε > 0, ∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ θ : ℝ,
      |θ| ≤ fragPermSaddleDeltaReal r →
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ ε) ∧
    (∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in fragPermRadFilter, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r)
        fragPermRadFilter (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
        fragPermSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt fragPermFun r n θ‖ ≤ E r)) := by
  exact ⟨fragPerm_local_uniform, fragPerm_tail_uniform⟩

lemma fragPermSaddleRadius_lt_one (n : ℕ) :
    fragPermSaddleRadius n < 1 := by
  unfold fragPermSaddleRadius
  have hden_pos : 0 < Real.sqrt (4 * (n : ℝ) + 1) + 1 := by positivity
  have hfrac_pos : 0 < 2 / (Real.sqrt (4 * (n : ℝ) + 1) + 1) := by positivity
  linarith

lemma fragPermSaddleAReal_radius (n : ℕ) :
    fragPermSaddleAReal (fragPermSaddleRadius n) = (n : ℝ) := by
  unfold fragPermSaddleAReal fragPermSaddleRadius
  let s : ℝ := Real.sqrt (4 * (n : ℝ) + 1)
  have hs_nonneg_arg : 0 ≤ 4 * (n : ℝ) + 1 := by positivity
  have hs_sq : s ^ 2 = 4 * (n : ℝ) + 1 := by
    dsimp [s]
    exact Real.sq_sqrt hs_nonneg_arg
  have hs_pos : 0 < s + 1 := by
    dsimp [s]
    positivity
  have hne : s + 1 ≠ 0 := hs_pos.ne'
  field_simp [hne]
  nlinarith

lemma fragPermSaddleRadius_tendsto_radFilter :
    Tendsto fragPermSaddleRadius atTop fragPermRadFilter := by
  unfold fragPermRadFilter
  rw [tendsto_nhdsWithin_iff]
  constructor
  · unfold fragPermSaddleRadius
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hmul : Tendsto (fun n : ℕ => (4 : ℝ) * (n : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) hn
    have hlin : Tendsto (fun n : ℕ => (4 : ℝ) * (n : ℝ) + 1) atTop atTop :=
      hmul.atTop_add tendsto_const_nhds
    have hden : Tendsto
        (fun n : ℕ => Real.sqrt (4 * (n : ℝ) + 1) + 1) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp hlin).atTop_add tendsto_const_nhds
    have hfrac : Tendsto
        (fun n : ℕ => (2 : ℝ) / (Real.sqrt (4 * (n : ℝ) + 1) + 1))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have hsub : Tendsto
        (fun n : ℕ => (1 : ℝ) -
          (2 : ℝ) / (Real.sqrt (4 * (n : ℝ) + 1) + 1))
        atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hfrac
    simpa using hsub
  · exact Eventually.of_forall fun n => fragPermSaddleRadius_lt_one n

end FragmentedPermHAdmissible
end
end

section
/-!
# Second-order saddle data for fragmented permutations

This file adds the second-order correction layer for
`exp (z / (1 - z))`.  The logarithmic saddle derivatives are
`b₃(r) = r(1 + 4r + r²)/(1-r)^4` and
`b₄(r) = r(1 + 11r + 11r² + r³)/(1-r)^5`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

namespace FragmentedPermHAdmissible

lemma fragPermSecondCorrScale_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < fragPermSecondCorrScale r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermSecondCorrScale
  linarith [hr.2]

lemma fragPermSecondCorrScale_tendsto_zero :
    Tendsto fragPermSecondCorrScale fragPermRadFilter (𝓝 0) := by
  have h :=
    fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  simpa [fragPermSecondCorrScale] using h

lemma fragPerm_saddleCorrectionScale_eq {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    saddleCorrectionScale fragPermSaddleBReal fragPermSaddleB3Real
        fragPermSaddleB4Real r =
      (1 - r) *
        ((1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (r * (1 + r) ^ 2) +
          (1 + 4 * r + r ^ 2) ^ 2 / (r * (1 + r) ^ 3)) := by
  have hu : 0 < 1 - r := by linarith
  have h1r : 0 < 1 + r := by positivity
  unfold saddleCorrectionScale fragPermSaddleBReal fragPermSaddleB3Real
    fragPermSaddleB4Real
  have hb4_nonneg :
      0 ≤ r * (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5 := by
    positivity
  rw [abs_of_nonneg hb4_nonneg]
  field_simp [hr.ne', hu.ne', h1r.ne']

lemma fragPerm_saddleCorrectionScale_le_oneSub_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      saddleCorrectionScale fragPermSaddleBReal fragPermSaddleB3Real
          fragPermSaddleB4Real r ≤ 200 * fragPermSecondCorrScale r := by
  filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hscale := fragPerm_saddleCorrectionScale_eq hrpos hr.2
  have hu_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
  have hrle : r ≤ 1 := hr.2.le
  have hpoly4_le : 1 + 11 * r + 11 * r ^ 2 + r ^ 3 ≤ 24 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1)]
  have hpoly3_le : 1 + 4 * r + r ^ 2 ≤ 6 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r)]
  have hpoly3_nonneg : 0 ≤ 1 + 4 * r + r ^ 2 := by positivity
  have hpoly3_sq_le : (1 + 4 * r + r ^ 2) ^ 2 ≤ 36 := by
    nlinarith [sq_nonneg (1 + 4 * r + r ^ 2), hpoly3_nonneg, hpoly3_le]
  have hden1_pos : 0 < r * (1 + r) ^ 2 := by positivity
  have hden2_pos : 0 < r * (1 + r) ^ 3 := by positivity
  have hden1_ge : (1 / 2 : ℝ) ≤ r * (1 + r) ^ 2 := by
    have hsq : 1 ≤ (1 + r) ^ 2 := by nlinarith [hrpos]
    have hmul := mul_le_mul_of_nonneg_left hsq hrpos.le
    nlinarith [hr.1, hmul]
  have hden2_ge : (1 / 2 : ℝ) ≤ r * (1 + r) ^ 3 := by
    have hcube : 1 ≤ (1 + r) ^ 3 := by
      nlinarith [hrpos, sq_nonneg (1 + r), sq_nonneg ((1 + r) - 1)]
    have hmul := mul_le_mul_of_nonneg_left hcube hrpos.le
    nlinarith [hr.1, hmul]
  have hterm1 :
      (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (r * (1 + r) ^ 2) ≤ 48 := by
    rw [div_le_iff₀ hden1_pos]
    nlinarith
  have hterm2 :
      (1 + 4 * r + r ^ 2) ^ 2 / (r * (1 + r) ^ 3) ≤ 72 := by
    rw [div_le_iff₀ hden2_pos]
    nlinarith
  rw [hscale]
  unfold fragPermSecondCorrScale
  calc
    (1 - r) *
        ((1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (r * (1 + r) ^ 2) +
          (1 + 4 * r + r ^ 2) ^ 2 / (r * (1 + r) ^ 3))
        ≤ (1 - r) * 120 := by
          exact mul_le_mul_of_nonneg_left (by linarith) hu_nonneg
    _ ≤ 200 * (1 - r) := by nlinarith

private lemma fragPermGaussianDom_nonneg (x : ℝ) : 0 ≤ fragPermGaussianDom x := by
  unfold fragPermGaussianDom
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

private lemma fragPermGaussianDom_integrable : Integrable fragPermGaussianDom := by
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
  unfold fragPermGaussianDom
  dsimp [g]
  ring_nf

private lemma fragPermGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, fragPermGaussianDom x := by
  exact integral_nonneg (fun x => fragPermGaussianDom_nonneg x)

private lemma fragPermGaussianDom_continuous : Continuous fragPermGaussianDom := by
  unfold fragPermGaussianDom
  fun_prop

private lemma fragPermGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, fragPermGaussianDom x) ≤ ∫ x : ℝ, fragPermGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral fragPermGaussianDom_integrable
    (Eventually.of_forall fragPermGaussianDom_nonneg)

private lemma fragPermSaddleBReal_pos_of_Ioo_half_one {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    0 < fragPermSaddleBReal r := by
  unfold fragPermSaddleBReal
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hnum : 0 < r * (1 + r) := by positivity
  have hden : 0 < (1 - r) ^ 3 := by positivity
  exact div_pos hnum hden

private lemma fragPermLocalL1Const_pos : 0 < fragPermLocalL1Const := by
  unfold fragPermLocalL1Const fragPermScaledRemainderConst fragPermLocalTaylorConst
  positivity

private lemma fragPerm_local_integrand_continuous (r : ℝ)
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖ := by
  have hr0 : 0 ≤ r := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1).le
  have hden_circle :
      ∀ x : ℝ,
        1 - (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hzero
    have hz :
        (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    have hexp_norm :
        ‖Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hnorm_left :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = r := by
      have hr_norm : ‖(r : ℂ)‖ = r :=
        (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_nonneg hr0)
      rw [norm_mul, hr_norm, hexp_norm, mul_one]
    have hnorm_one :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [hz]
      norm_num
    linarith [hr.2]
  have hden_real : (1 : ℂ) - (r : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith [hr.2]
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))) -
            saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖ := by
    have hzcont :
        Continuous fun x : ℝ =>
          (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hfragCircle :
        Continuous fun x : ℝ =>
          fragPermH ((r : ℂ) *
            Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)) := by
      unfold fragPermH
      exact hzcont.div (continuous_const.sub hzcont) hden_circle
    have hlin :
        Continuous fun x : ℝ =>
          ((fragPermSaddleAReal r * (x / Real.sqrt (fragPermSaddleBReal r)) : ℝ) : ℂ) *
            Complex.I := by
      fun_prop
    have hquad :
        Continuous fun x : ℝ =>
          ((fragPermSaddleBReal r * (x / Real.sqrt (fragPermSaddleBReal r)) ^ 2 / 2 : ℝ) : ℂ) := by
      fun_prop
    have hlocal :
        Continuous fun x : ℝ =>
          fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) := by
      unfold fragPermLocalExponent
      exact ((hfragCircle.sub continuous_const).sub hlin).add hquad
    have hsaddle :
        Continuous fun x : ℝ =>
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x := by
      unfold saddleSecondPoly
      fun_prop
    have hgauss : Continuous fun x : ℝ => Complex.exp (-(x ^ 2) / 2) := by
      fun_prop
    exact (hgauss.mul ((Complex.continuous_exp.comp hlocal).sub hsaddle)).norm
  simpa [fragPerm_saddleLocalRatio_eq] using h

/--
The remaining local analytic estimate for fragmented permutations: after
scaling `θ = x / sqrt b(r)`, the exact local-ratio identity
`fragPerm_saddleLocalRatio_eq` admits a fifth-order expansion whose Gaussian
`L¹` remainder is `o(1-r)`.  This is the same Taylor/Gaussian-domination
calculation as the completed involution and Bell files, with the rational
finite-radius algebra for `z/(1-z)`.
-/
theorem fragPerm_local_second_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real r x)‖) /
            fragPermSecondCorrScale r)
        fragPermRadFilter (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, fragPermGaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact fragPermGaussianDom_integral_nonneg
  have hsqrt_tendsto :
      Tendsto (fun r : ℝ => Real.sqrt (1 - r)) fragPermRadFilter (𝓝 0) := by
    have hu :
        Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
      fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
    have h := hu.sqrt
    simpa using h
  have hupper_tendsto :
      Tendsto
        (fun r : ℝ => fragPermLocalL1Const * M * Real.sqrt (1 - r))
        fragPermRadFilter (𝓝 0) := by
    simpa [mul_assoc] using hsqrt_tendsto.const_mul (fragPermLocalL1Const * M)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [fragPerm_eventually_Ioo_zero_one, fragPermSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, fragPermSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [fragPerm_eventually_Ioo_half_one, fragPerm_delta_le_one_eventually,
      fragPerm_delta_le_one_sub_quarter_eventually,
      fragPermLocalBound_tendsto_zero.eventually_le_const zero_lt_one,
      fragPermSecondCorrScale_pos_eventually] with
      r hr hδle hδu hlocSmall hcorrPos
    let L : ℝ := fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖
    let H : ℝ → ℝ := fun x =>
      (fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r))) * fragPermGaussianDom x
    have hbpos : 0 < fragPermSaddleBReal r := fragPermSaddleBReal_pos_of_Ioo_half_one hr
    have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
    have hLnonneg : 0 ≤ L := by
      dsimp [L, fragPermSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ H x := by
      intro x hx
      have hxabs : |x| ≤ L := by
        exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hθδ : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermSaddleDeltaReal r := by
        rw [abs_div, abs_of_pos hsqrt_pos]
        calc
          |x| / Real.sqrt (fragPermSaddleBReal r) ≤
              L / Real.sqrt (fragPermSaddleBReal r) :=
            div_le_div_of_nonneg_right hxabs hsqrt_pos.le
          _ = fragPermSaddleDeltaReal r := by
            dsimp [L]
            exact mul_div_cancel_right₀ (fragPermSaddleDeltaReal r) hsqrt_pos.ne'
      have hWnorm :
          ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1 :=
        (fragPerm_local_exponent_norm_le
          (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1).le hr.2 hδle hδu hθδ).trans hlocSmall
      have hb := fragPerm_local_integrand_bound hr hθδ hδle hδu hWnorm
      dsimp [F, H]
      exact hb
    have hFint : IntervalIntegrable F volume (-L) L := by
      exact (fragPerm_local_integrand_continuous r hr).intervalIntegrable _ _
    have hHint : IntervalIntegrable H volume (-L) L := by
      exact (fragPermGaussianDom_continuous.const_mul
        (fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r)))).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤
          (fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r))) * M := by
      have hconst_nonneg :
          0 ≤ fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r)) := by
        have hu_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
        exact mul_nonneg fragPermLocalL1Const_pos.le
          (mul_nonneg hu_nonneg (Real.sqrt_nonneg _))
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, H x :=
          intervalIntegral.integral_mono_on hle hFint hHint hpoint
        _ = (fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r))) *
              (∫ x in -L..L, fragPermGaussianDom x) := by
          dsimp [H]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r))) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact fragPermGaussianDom_window_le_integral hLnonneg)
            hconst_nonneg
    have hmain :
        (∫ x in -L..L, F x) / fragPermSecondCorrScale r ≤
          ((fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r))) * M) /
            fragPermSecondCorrScale r := by
      exact div_le_div_of_nonneg_right hIntBound hcorrPos.le
    have hu_pos : 0 < 1 - r := by
      simpa [fragPermSecondCorrScale] using hcorrPos
    calc
      ((∫ x in -(fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real r x)‖) /
          fragPermSecondCorrScale r)
          = (∫ x in -L..L, F x) / fragPermSecondCorrScale r := by rfl
      _ ≤ ((fragPermLocalL1Const * ((1 - r) * Real.sqrt (1 - r))) * M) /
            fragPermSecondCorrScale r := hmain
      _ = fragPermLocalL1Const * M * Real.sqrt (1 - r) := by
        unfold fragPermSecondCorrScale
        field_simp [hu_pos.ne']

end FragmentedPermHAdmissible
end
end

/-!
# Third-order saddle data for fragmented permutations

This file adds the finite-radius third-order correction layer for
`exp (z / (1 - z))`.  The proof uses the narrower finite-radius window
`(1-r)^(29/20)`, because the second-order window is too wide for an
`o((1-r)^2)` third-order remainder.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

noncomputable section

namespace FragmentedPermHAdmissible

/-- True third-order correction scale for the finite-radius fragmented-permutation saddle. -/
def fragPermThirdCorrScale (r : ℝ) : ℝ :=
  (1 - r) ^ 2

/-- Error term for the fragmented-permutation EGF coefficient through third order. -/
def fragPermThirdOrderSeriesError (n : ℕ) : ℂ :=
  fragPermSeries.coeff n / fragPermThirdOrderSaddleScale n -
    (1 + (fragPermSecondCorrectionAtSaddle n : ℂ) +
      (fragPermThirdCorrectionAtSaddle n : ℂ))

lemma fragPermThirdCorrScale_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < fragPermThirdCorrScale r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermThirdCorrScale
  exact sq_pos_of_pos (by linarith [hr.2] : 0 < 1 - r)

lemma fragPermThirdCorrScale_tendsto_zero :
    Tendsto fragPermThirdCorrScale fragPermRadFilter (𝓝 0) := by
  have h :
      Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
    fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  simpa [fragPermThirdCorrScale] using h.pow 2

lemma fragPerm_one_sub_rpow_neg_one_twentieth_tendsto_atTop :
    Tendsto (fun r : ℝ => (1 - r) ^ (-(1 / 20 : ℝ))) fragPermRadFilter atTop := by
  have hinv : Tendsto (fun r : ℝ => (1 - r)⁻¹) fragPermRadFilter atTop :=
    tendsto_inv_nhdsGT_zero.comp fragPerm_one_sub_tendsto_nhdsGT_zero
  have hpow : Tendsto (fun r : ℝ => ((1 - r)⁻¹) ^ (1 / 20 : ℝ))
      fragPermRadFilter atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hinv
  refine Tendsto.congr' ?_ hpow
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hnonneg : 0 ≤ 1 - r := by linarith [hr.2]
  rw [Real.inv_rpow hnonneg]
  rw [← Real.rpow_neg hnonneg]

lemma fragPerm_third_delta_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < fragPermThirdSaddleDeltaReal r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermThirdSaddleDeltaReal
  exact Real.rpow_pos_of_pos (by linarith [hr.2] : 0 < 1 - r) _

lemma fragPerm_third_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, fragPermThirdSaddleDeltaReal r ≤ Real.pi := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hbase_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
  have hbase_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  have hδ_le_one : fragPermThirdSaddleDeltaReal r ≤ 1 := by
    unfold fragPermThirdSaddleDeltaReal
    exact Real.rpow_le_one hbase_nonneg hbase_le_one
      (by norm_num : (0 : ℝ) ≤ 29 / 20)
  have hpi : (1 : ℝ) ≤ Real.pi := by
    nlinarith [Real.one_le_pi_div_two]
  exact hδ_le_one.trans hpi

lemma fragPerm_third_delta_le_one_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, fragPermThirdSaddleDeltaReal r ≤ 1 := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hbase_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
  have hbase_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  unfold fragPermThirdSaddleDeltaReal
  exact Real.rpow_le_one hbase_nonneg hbase_le_one
    (by norm_num : (0 : ℝ) ≤ 29 / 20)

lemma fragPerm_third_delta_le_second_delta_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      fragPermThirdSaddleDeltaReal r ≤ fragPermSaddleDeltaReal r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  unfold fragPermThirdSaddleDeltaReal fragPermSaddleDeltaReal
  exact Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one
    (by norm_num : (7 / 5 : ℝ) ≤ 29 / 20)

lemma fragPerm_third_delta_le_one_sub_quarter_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      fragPermThirdSaddleDeltaReal r ≤ (1 - r) / 4 := by
  filter_upwards [fragPerm_third_delta_le_second_delta_eventually,
    fragPerm_delta_le_one_sub_quarter_eventually] with r hle hbase
  exact hle.trans hbase

lemma fragPerm_third_delta_sq_le_one_sub_sq_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      (fragPermThirdSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2 := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  have hu_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  calc
    (fragPermThirdSaddleDeltaReal r) ^ 2 = (1 - r) ^ (29 / 10 : ℝ) := by
      unfold fragPermThirdSaddleDeltaReal
      rw [← Real.rpow_mul_natCast hu_nonneg (29 / 20 : ℝ) 2]
      norm_num
    _ ≤ (1 - r) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one
        (by norm_num : (2 : ℝ) ≤ 29 / 10)
    _ = (1 - r) ^ 2 := by norm_num [Real.rpow_natCast]

lemma fragPerm_third_delta_sqrt_b_tendsto_atTop :
    Tendsto
      (fun r : ℝ => fragPermThirdSaddleDeltaReal r *
        Real.sqrt (fragPermSaddleBReal r))
      fragPermRadFilter atTop := by
  have hbase :
      Tendsto (fun r : ℝ => (1 / 2 : ℝ) *
        (1 - r) ^ (-(1 / 20 : ℝ))) fragPermRadFilter atTop :=
    (fragPerm_one_sub_rpow_neg_one_twentieth_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2))
  refine tendsto_atTop_mono' fragPermRadFilter ?_ hbase
  filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  have hsqrt := fragPerm_sqrt_b_lower_of_Ioo_half_one hr
  calc
    (1 / 2 : ℝ) * (1 - r) ^ (-(1 / 20 : ℝ))
        = fragPermThirdSaddleDeltaReal r *
            ((1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ))) := by
          unfold fragPermThirdSaddleDeltaReal
          calc
            (1 / 2 : ℝ) * (1 - r) ^ (-(1 / 20 : ℝ))
                = (1 / 2 : ℝ) *
                    ((1 - r) ^ (29 / 20 : ℝ) *
                      (1 - r) ^ (-(3 / 2 : ℝ))) := by
                  rw [← Real.rpow_add hu_pos]
                  norm_num
            _ = (1 - r) ^ (29 / 20 : ℝ) *
                ((1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ))) := by ring
    _ ≤ fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r) := by
          exact mul_le_mul_of_nonneg_left hsqrt
            (Real.rpow_nonneg hu_nonneg _)

lemma fragPermSaddleB5Real_nonneg_of_Ioo_zero_one {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ fragPermSaddleB5Real r := by
  unfold fragPermSaddleB5Real
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hr0 : 0 ≤ r := hr.1.le
  have hden : 0 < (1 - r) ^ 6 := pow_pos hu_pos _
  have hnum : 0 ≤ r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) := by
    positivity
  exact div_nonneg hnum hden.le

lemma fragPermSaddleB6Real_nonneg_of_Ioo_zero_one {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ fragPermSaddleB6Real r := by
  unfold fragPermSaddleB6Real
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hr0 : 0 ≤ r := hr.1.le
  have hden : 0 < (1 - r) ^ 7 := pow_pos hu_pos _
  have hnum :
      0 ≤ r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) := by
    positivity
  exact div_nonneg hnum hden.le

lemma fragPerm_saddleThirdCorrectionScale_le_sq_eventually :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in fragPermRadFilter,
        |fragPermSaddleB6Real r| / (fragPermSaddleBReal r) ^ 3
          + |fragPermSaddleB3Real r * fragPermSaddleB5Real r| /
              (fragPermSaddleBReal r) ^ 4
          + (fragPermSaddleB4Real r) ^ 2 / (fragPermSaddleBReal r) ^ 4
          + (fragPermSaddleB3Real r) ^ 2 * |fragPermSaddleB4Real r| /
              (fragPermSaddleBReal r) ^ 5
          + (fragPermSaddleB3Real r) ^ 4 / (fragPermSaddleBReal r) ^ 6
            ≤ K * fragPermThirdCorrScale r := by
  refine ⟨150000, by norm_num, ?_⟩
  filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
  let u : ℝ := 1 - r
  have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
  have hr0 : 0 ≤ r := hrpos.le
  have hrle : r ≤ 1 := hr.2.le
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hbpos : 0 < fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hnum : 0 < r * (1 + r) := by positivity
    have hden : 0 < (1 - r) ^ 3 := by positivity
    exact div_pos hnum hden
  have hb3_nonneg : 0 ≤ fragPermSaddleB3Real r := by
    unfold fragPermSaddleB3Real
    positivity
  have hb4_nonneg : 0 ≤ fragPermSaddleB4Real r := by
    unfold fragPermSaddleB4Real
    positivity
  have hb5_nonneg : 0 ≤ fragPermSaddleB5Real r :=
    fragPermSaddleB5Real_nonneg_of_Ioo_zero_one
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1, hr.2⟩
  have hb6_nonneg : 0 ≤ fragPermSaddleB6Real r :=
    fragPermSaddleB6Real_nonneg_of_Ioo_zero_one
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1, hr.2⟩
  have hB_lower : (1 / 2 : ℝ) / u ^ 3 ≤ fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 3 := by positivity
    have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
    exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
  have hB_inv_le : (fragPermSaddleBReal r)⁻¹ ≤ 2 * u ^ 3 := by
    have hlow_pos : 0 < (1 / 2 : ℝ) / u ^ 3 := by positivity
    have hmul := inv_anti₀ hlow_pos hB_lower
    calc
      (fragPermSaddleBReal r)⁻¹ ≤ ((1 / 2 : ℝ) / u ^ 3)⁻¹ := hmul
      _ = 2 * u ^ 3 := by field_simp [hu_pos.ne']
  have hpoly3_le : 1 + 4 * r + r ^ 2 ≤ 6 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r)]
  have hpoly4_le : 1 + 11 * r + 11 * r ^ 2 + r ^ 3 ≤ 24 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1)]
  have hpoly5_le :
      1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4 ≤ 120 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1),
      show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity]
  have hpoly6_le :
      1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4 ≤ 360 := by
    nlinarith [hr.1, hrle, sq_nonneg r, sq_nonneg (1 - r), sq_nonneg (r - 1),
      show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity]
  have hb3_le : fragPermSaddleB3Real r ≤ 6 / u ^ 4 := by
    unfold fragPermSaddleB3Real
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 4 := by positivity
    calc
      r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4
          ≤ 1 * 6 / (1 - r) ^ 4 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul hrle hpoly3_le (by positivity) zero_le_one) hden_pos.le
      _ = 6 / u ^ 4 := by ring
  have hb4_le : fragPermSaddleB4Real r ≤ 24 / u ^ 5 := by
    unfold fragPermSaddleB4Real
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 5 := by positivity
    calc
      r * (1 + 11 * r + 11 * r ^ 2 + r ^ 3) / (1 - r) ^ 5
          ≤ 1 * 24 / (1 - r) ^ 5 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul hrle hpoly4_le (by positivity) zero_le_one) hden_pos.le
      _ = 24 / u ^ 5 := by ring
  have hb5_le : fragPermSaddleB5Real r ≤ 120 / u ^ 6 := by
    unfold fragPermSaddleB5Real
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 6 := by positivity
    calc
      r * (1 + 26 * r + 66 * r ^ 2 + 26 * r ^ 3 + r ^ 4) / (1 - r) ^ 6
          ≤ 1 * 120 / (1 - r) ^ 6 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul hrle hpoly5_le (by positivity) zero_le_one) hden_pos.le
      _ = 120 / u ^ 6 := by ring
  have hb6_le : fragPermSaddleB6Real r ≤ 720 / u ^ 7 := by
    unfold fragPermSaddleB6Real
    dsimp [u]
    have hden_pos : 0 < (1 - r) ^ 7 := by positivity
    have hnum_le :
        r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) ≤
          2 * 360 := by
      have hr1_le_two : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hrle]
      exact mul_le_mul hr1_le_two hpoly6_le (by positivity) (by positivity)
    calc
      r * (1 + r) * (1 + 56 * r + 246 * r ^ 2 + 56 * r ^ 3 + r ^ 4) /
          (1 - r) ^ 7
          ≤ 720 / (1 - r) ^ 7 := by
            exact div_le_div_of_nonneg_right (by nlinarith [hnum_le]) hden_pos.le
      _ = 720 / u ^ 7 := by dsimp [u]
  have hterm1 :
      |fragPermSaddleB6Real r| / (fragPermSaddleBReal r) ^ 3 ≤ 5760 * u ^ 2 := by
    rw [abs_of_nonneg hb6_nonneg]
    rw [div_eq_mul_inv, ← inv_pow]
    calc
      fragPermSaddleB6Real r * (fragPermSaddleBReal r)⁻¹ ^ 3
          ≤ (720 / u ^ 7) * (2 * u ^ 3) ^ 3 := by
            exact mul_le_mul hb6_le
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 3)
              (by positivity) (by positivity)
      _ = 5760 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  have hterm2 :
      |fragPermSaddleB3Real r * fragPermSaddleB5Real r| /
          (fragPermSaddleBReal r) ^ 4 ≤ 11520 * u ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hb3_nonneg hb5_nonneg)]
    rw [div_eq_mul_inv, ← inv_pow]
    have hnum :
        fragPermSaddleB3Real r * fragPermSaddleB5Real r ≤
          (6 / u ^ 4) * (120 / u ^ 6) :=
      mul_le_mul hb3_le hb5_le hb5_nonneg (by positivity)
    calc
      fragPermSaddleB3Real r * fragPermSaddleB5Real r *
            (fragPermSaddleBReal r)⁻¹ ^ 4
          ≤ ((6 / u ^ 4) * (120 / u ^ 6)) * (2 * u ^ 3) ^ 4 := by
            exact mul_le_mul hnum
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 4)
              (by positivity) (by positivity)
      _ = 11520 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  have hterm3 :
      (fragPermSaddleB4Real r) ^ 2 / (fragPermSaddleBReal r) ^ 4 ≤
          9216 * u ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    have hnum : (fragPermSaddleB4Real r) ^ 2 ≤ (24 / u ^ 5) ^ 2 :=
      pow_le_pow_left₀ hb4_nonneg hb4_le 2
    calc
      (fragPermSaddleB4Real r) ^ 2 * (fragPermSaddleBReal r)⁻¹ ^ 4
          ≤ (24 / u ^ 5) ^ 2 * (2 * u ^ 3) ^ 4 := by
            exact mul_le_mul hnum
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 4)
              (by positivity) (sq_nonneg _)
      _ = 9216 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  have hterm4 :
      (fragPermSaddleB3Real r) ^ 2 * |fragPermSaddleB4Real r| /
          (fragPermSaddleBReal r) ^ 5 ≤ 27648 * u ^ 2 := by
    rw [abs_of_nonneg hb4_nonneg]
    rw [div_eq_mul_inv, ← inv_pow]
    have hnum :
        (fragPermSaddleB3Real r) ^ 2 * fragPermSaddleB4Real r ≤
          (6 / u ^ 4) ^ 2 * (24 / u ^ 5) :=
      mul_le_mul (pow_le_pow_left₀ hb3_nonneg hb3_le 2) hb4_le
        (by positivity) (sq_nonneg _)
    calc
      (fragPermSaddleB3Real r) ^ 2 * fragPermSaddleB4Real r *
            (fragPermSaddleBReal r)⁻¹ ^ 5
          ≤ ((6 / u ^ 4) ^ 2 * (24 / u ^ 5)) * (2 * u ^ 3) ^ 5 := by
            exact mul_le_mul hnum
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 5)
              (by positivity) (by positivity)
      _ = 27648 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  have hterm5 :
      (fragPermSaddleB3Real r) ^ 4 / (fragPermSaddleBReal r) ^ 6 ≤
          82944 * u ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    have hnum : (fragPermSaddleB3Real r) ^ 4 ≤ (6 / u ^ 4) ^ 4 :=
      pow_le_pow_left₀ hb3_nonneg hb3_le 4
    calc
      (fragPermSaddleB3Real r) ^ 4 * (fragPermSaddleBReal r)⁻¹ ^ 6
          ≤ (6 / u ^ 4) ^ 4 * (2 * u ^ 3) ^ 6 := by
            exact mul_le_mul hnum
              (pow_le_pow_left₀ (inv_nonneg.mpr hbpos.le) hB_inv_le 6)
              (by positivity) (by positivity)
      _ = 82944 * u ^ 2 := by field_simp [hu_pos.ne']; ring
  unfold fragPermThirdCorrScale
  dsimp [u] at hterm1 hterm2 hterm3 hterm4 hterm5 ⊢
  nlinarith [hterm1, hterm2, hterm3, hterm4, hterm5]

/-- Near-tail envelope for the third-order finite-radius window. -/
def fragPermThirdNearTailE (r : ℝ) : ℝ :=
  2 * Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)))

/-- Combined third-order finite-radius tail envelope. -/
def fragPermThirdTailE (r : ℝ) : ℝ :=
  fragPermThirdNearTailE r + fragPermTailE r

lemma saddleGAt_norm_eq_gaussian_mul_saddleLocalRatio_norm
    (f : ℂ → ℂ) (a b : ℝ → ℝ) (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt f r n θ‖ =
      Real.exp (-(b r * θ ^ 2 / 2)) *
        ‖saddleLocalRatio f a b r θ‖ := by
  let A : ℂ := f ((r : ℂ) * Complex.exp (θ * Complex.I)) / f (r : ℂ)
  let Pn : ℂ := Complex.exp (-(↑↑n * ↑θ) * Complex.I)
  let Pa : ℂ := Complex.exp (-(a r * θ : ℝ) * Complex.I)
  let G : ℂ := Complex.exp (-(b r * θ ^ 2 / 2 : ℝ))
  have hPn : ‖Pn‖ = 1 := by
    dsimp [Pn]
    rw [Complex.norm_exp]
    simp
  have hPa : ‖Pa‖ = 1 := by
    dsimp [Pa]
    rw [Complex.norm_exp]
    simp
  have hGnorm : ‖G‖ = Real.exp (-(b r * θ ^ 2 / 2)) := by
    dsimp [G]
    rw [Complex.norm_exp]
    congr 1
  have hGpos : 0 < Real.exp (-(b r * θ ^ 2 / 2)) := Real.exp_pos _
  unfold saddleGAt saddleLocalRatio
  change ‖A * Pn‖ = Real.exp (-(b r * θ ^ 2 / 2)) * ‖A * Pa / G‖
  rw [norm_mul, hPn, mul_one]
  have hdivnorm : ‖A * Pa / G‖ = ‖A * Pa‖ / ‖G‖ := by
    rw [norm_div]
  rw [hdivnorm]
  rw [norm_mul, hPa, mul_one, hGnorm]
  field_simp [hGpos.ne']

lemma fragPermThirdNearTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 ≤ fragPermThirdNearTailE r :=
  Eventually.of_forall fun _ => by
    unfold fragPermThirdNearTailE
    positivity

lemma fragPermThirdTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 ≤ fragPermThirdTailE r := by
  filter_upwards [fragPermThirdNearTailE_nonneg_eventually,
    fragPermTailE_nonneg_eventually] with r hnear hfar
  unfold fragPermThirdTailE
  positivity

lemma fragPerm_one_sub_rpow_neg_one_tenth_tendsto_atTop :
    Tendsto (fun r : ℝ => (1 - r) ^ (-(1 / 10 : ℝ))) fragPermRadFilter atTop :=
  fragPerm_one_sub_rpow_neg_tendsto_atTop

lemma fragPermThirdNearTailE_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * fragPermThirdNearTailE r /
          fragPermThirdCorrScale r)
      fragPermRadFilter (𝓝 0) := by
  let c : ℝ := (1 / 4 : ℝ)
  have hc : 0 < c := by norm_num [c]
  have hbase :
      Tendsto (fun y : ℝ => y ^ (35 : ℝ) * Real.exp (-c * y))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (35 : ℝ) c hc
  have hy := fragPerm_one_sub_rpow_neg_one_tenth_tendsto_atTop
  have hcomp :
      Tendsto
        (fun r : ℝ => ((1 - r) ^ (-(1 / 10 : ℝ))) ^ (35 : ℝ) *
          Real.exp (-c * ((1 - r) ^ (-(1 / 10 : ℝ)))))
        fragPermRadFilter (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto
        (fun r : ℝ => 2 * Real.sqrt (4 * Real.pi) *
          (((1 - r) ^ (-(1 / 10 : ℝ))) ^ (35 : ℝ) *
            Real.exp (-c * ((1 - r) ^ (-(1 / 10 : ℝ))))))
        fragPermRadFilter (𝓝 0) := by
    simpa using hcomp.const_mul (2 * Real.sqrt (4 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · filter_upwards [fragPermThirdCorrScale_pos_eventually] with r hcorr
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by unfold fragPermThirdNearTailE; positivity))
      hcorr.le
  · filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
    let u : ℝ := 1 - r
    have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have hnum_le : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hr.2]
    have hB_le : fragPermSaddleBReal r ≤ 2 / u ^ 3 := by
      unfold fragPermSaddleBReal
      dsimp [u]
      have hden_pos : 0 < (1 - r) ^ 3 := by positivity
      exact div_le_div_of_nonneg_right hnum_le hden_pos.le
    have hmul : 2 * Real.pi * fragPermSaddleBReal r ≤ 4 * Real.pi / u ^ 3 := by
      calc
        2 * Real.pi * fragPermSaddleBReal r
            ≤ 2 * Real.pi * (2 / u ^ 3) :=
              mul_le_mul_of_nonneg_left hB_le (by positivity)
        _ = 4 * Real.pi / u ^ 3 := by ring
    have hsqrt :
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) ≤
          Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
      calc
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r)
            ≤ Real.sqrt (4 * Real.pi / u ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
          have h4pi : 0 ≤ 4 * Real.pi := by positivity
          rw [div_eq_mul_inv]
          rw [Real.sqrt_mul h4pi]
          have hsqrt_inv_u3 : Real.sqrt ((u ^ 3)⁻¹) = u ^ (-(3 / 2 : ℝ)) := by
            have hinv_u3 : (u ^ 3)⁻¹ = u ^ (-3 : ℝ) := by
              rw [show u ^ 3 = u ^ (3 : ℝ) by exact (Real.rpow_natCast u 3).symm]
              rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
            rw [hinv_u3]
            rw [Real.sqrt_eq_rpow]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
          congr 1
    have hy_pow :
        ((1 - r) ^ (-(1 / 10 : ℝ))) ^ (35 : ℝ) =
          u ^ (-(7 / 2 : ℝ)) := by
      have h :
          ((1 - r) ^ (-(1 / 10 : ℝ))) ^ (35 : ℝ) =
            (1 - r) ^ (-(7 / 2 : ℝ)) := by
        rw [← Real.rpow_mul (by linarith : 0 ≤ 1 - r)]
        norm_num
      simpa [u] using h
    have hpow_div : u ^ (-(3 / 2 : ℝ)) / u ^ 2 = u ^ (-(7 / 2 : ℝ)) := by
      rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hu_nonneg (2 : ℝ)]
      rw [← Real.rpow_add hu_pos]
      norm_num
    unfold fragPermThirdNearTailE fragPermThirdCorrScale
    dsimp [c]
    rw [hy_pow]
    calc
      Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) *
            (2 * Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)))) /
          (1 - r) ^ 2
          ≤ (Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ))) *
              (2 * Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)))) /
            u ^ 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsqrt (by positivity))
              (by positivity)
      _ = 2 * Real.sqrt (4 * Real.pi) *
            (u ^ (-(7 / 2 : ℝ)) *
              Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)))) := by
            calc
              Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) *
                    (2 * Real.exp (-(1 / 4 : ℝ) *
                      (1 - r) ^ (-(1 / 10 : ℝ)))) / u ^ 2
                  =
                    2 * Real.sqrt (4 * Real.pi) *
                      ((u ^ (-(3 / 2 : ℝ)) / u ^ 2) *
                        Real.exp (-(1 / 4 : ℝ) *
                          (1 - r) ^ (-(1 / 10 : ℝ)))) := by
                    field_simp [hu_pos.ne']
              _ = 2 * Real.sqrt (4 * Real.pi) *
                    (u ^ (-(7 / 2 : ℝ)) *
                      Real.exp (-(1 / 4 : ℝ) *
                        (1 - r) ^ (-(1 / 10 : ℝ)))) := by
                    rw [hpow_div]

lemma fragPermTailE_third_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * fragPermTailE r /
          fragPermThirdCorrScale r)
      fragPermRadFilter (𝓝 0) := by
  let c : ℝ := fragPermTailC
  have hc : 0 < c := by
    dsimp [c, fragPermTailC]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (35 / 2 : ℝ) * Real.exp (-c * y))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (35 / 2 : ℝ) c hc
  have hy := fragPerm_one_sub_rpow_neg_one_fifth_tendsto_atTop
  have hcomp :
      Tendsto
        (fun r : ℝ => ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (35 / 2 : ℝ) *
          Real.exp (-c * ((1 - r) ^ (-(1 / 5 : ℝ)))))
        fragPermRadFilter (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto
        (fun r : ℝ => Real.sqrt (4 * Real.pi) *
          (((1 - r) ^ (-(1 / 5 : ℝ))) ^ (35 / 2 : ℝ) *
            Real.exp (-c * ((1 - r) ^ (-(1 / 5 : ℝ))))))
        fragPermRadFilter (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (4 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · filter_upwards [fragPermThirdCorrScale_pos_eventually] with r hcorr
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) hcorr.le
  · filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
    let u : ℝ := 1 - r
    have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have hnum_le : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hr.2]
    have hB_le : fragPermSaddleBReal r ≤ 2 / u ^ 3 := by
      unfold fragPermSaddleBReal
      dsimp [u]
      have hden_pos : 0 < (1 - r) ^ 3 := by positivity
      exact div_le_div_of_nonneg_right hnum_le hden_pos.le
    have hmul : 2 * Real.pi * fragPermSaddleBReal r ≤ 4 * Real.pi / u ^ 3 := by
      calc
        2 * Real.pi * fragPermSaddleBReal r
            ≤ 2 * Real.pi * (2 / u ^ 3) :=
              mul_le_mul_of_nonneg_left hB_le (by positivity)
        _ = 4 * Real.pi / u ^ 3 := by ring
    have hsqrt :
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) ≤
          Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
      calc
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r)
            ≤ Real.sqrt (4 * Real.pi / u ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
          have h4pi : 0 ≤ 4 * Real.pi := by positivity
          rw [div_eq_mul_inv]
          rw [Real.sqrt_mul h4pi]
          have hsqrt_inv_u3 : Real.sqrt ((u ^ 3)⁻¹) = u ^ (-(3 / 2 : ℝ)) := by
            have hinv_u3 : (u ^ 3)⁻¹ = u ^ (-3 : ℝ) := by
              rw [show u ^ 3 = u ^ (3 : ℝ) by exact (Real.rpow_natCast u 3).symm]
              rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
            rw [hinv_u3]
            rw [Real.sqrt_eq_rpow]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
          congr 1
    have hy_pow :
        ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (35 / 2 : ℝ) =
          u ^ (-(7 / 2 : ℝ)) := by
      have h :
          ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (35 / 2 : ℝ) =
            (1 - r) ^ (-(7 / 2 : ℝ)) := by
        rw [← Real.rpow_mul (by linarith : 0 ≤ 1 - r)]
        norm_num
      simpa [u] using h
    have hpow_div : u ^ (-(3 / 2 : ℝ)) / u ^ 2 = u ^ (-(7 / 2 : ℝ)) := by
      rw [show u ^ 2 = u ^ (2 : ℝ) by exact (Real.rpow_natCast u 2).symm]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg hu_nonneg (2 : ℝ)]
      rw [← Real.rpow_add hu_pos]
      norm_num
    unfold fragPermTailE fragPermThirdCorrScale
    dsimp [c, fragPermTailC]
    rw [hy_pow]
    calc
      Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) *
            Real.exp (-(1 / (4 * Real.pi ^ 2)) *
              (1 - r) ^ (-(1 / 5 : ℝ))) / (1 - r) ^ 2
          ≤ (Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ))) *
              Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                (1 - r) ^ (-(1 / 5 : ℝ))) / u ^ 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le)
              (by positivity)
      _ = Real.sqrt (4 * Real.pi) *
            (u ^ (-(7 / 2 : ℝ)) *
              Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                (1 - r) ^ (-(1 / 5 : ℝ)))) := by
            calc
              Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) *
                    Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                      (1 - r) ^ (-(1 / 5 : ℝ))) / u ^ 2
                  =
                    Real.sqrt (4 * Real.pi) *
                      ((u ^ (-(3 / 2 : ℝ)) / u ^ 2) *
                        Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                          (1 - r) ^ (-(1 / 5 : ℝ)))) := by
                    field_simp [hu_pos.ne']
              _ = Real.sqrt (4 * Real.pi) *
                    (u ^ (-(7 / 2 : ℝ)) *
                      Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                        (1 - r) ^ (-(1 / 5 : ℝ)))) := by
                    rw [hpow_div]

lemma fragPermThirdTailE_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * fragPermThirdTailE r /
          fragPermThirdCorrScale r)
      fragPermRadFilter (𝓝 0) := by
  have hnear := fragPermThirdNearTailE_decay
  have hfar := fragPermTailE_third_decay
  have hsum := hnear.add hfar
  simpa [fragPermThirdTailE, mul_add, add_div] using hsum

lemma fragPerm_third_tail_bound_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
      fragPermThirdSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt fragPermFun r n θ‖ ≤ fragPermThirdTailE r := by
  have hlocal := fragPerm_local_uniform 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [fragPerm_eventually_Ioo_half_one, fragPerm_third_delta_sq_le_one_sub_sq_eventually,
    fragPerm_third_delta_le_second_delta_eventually, hlocal, fragPerm_tail_bound_eventually] with
      r hr hδ3sq hδ3_le_old hloc hfar n θ hθδ3 hθπ
  by_cases hnear : |θ| ≤ fragPermSaddleDeltaReal r
  · have hbpos : 0 < fragPermSaddleBReal r := by
      unfold fragPermSaddleBReal
      have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
      have hu_pos' : 0 < 1 - r := by linarith [hr.2]
      have hnum : 0 < r * (1 + r) := by positivity
      have hden : 0 < (1 - r) ^ 3 := pow_pos hu_pos' _
      exact div_pos hnum hden
    have hratio_close :
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ 1 :=
      hloc θ hnear
    have hratio_norm :
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ‖ ≤ 2 := by
      calc
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ‖
            = ‖(saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1) +
                1‖ := by ring_nf
        _ ≤ ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ +
              ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 2 := by norm_num at hratio_close ⊢; linarith
    have hu_pos : 0 < 1 - r := by linarith [hr.2]
    have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
    have hB_lower : (1 / 2 : ℝ) / (1 - r) ^ 3 ≤ fragPermSaddleBReal r := by
      unfold fragPermSaddleBReal
      have hden_pos : 0 < (1 - r) ^ 3 := by positivity
      have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
      exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
    have hθsq : (fragPermThirdSaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
      have hδ_nonneg : 0 ≤ fragPermThirdSaddleDeltaReal r := by
        unfold fragPermThirdSaddleDeltaReal
        exact Real.rpow_nonneg hu_nonneg _
      calc
        (fragPermThirdSaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ hδ_nonneg hθδ3 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hscale_lower :
        (1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)) ≤
          fragPermSaddleBReal r * θ ^ 2 / 2 := by
      have hδsq_eq :
          (fragPermThirdSaddleDeltaReal r) ^ 2 =
            (1 - r) ^ (29 / 10 : ℝ) := by
        unfold fragPermThirdSaddleDeltaReal
        rw [← Real.rpow_mul_natCast hu_nonneg (29 / 20 : ℝ) 2]
        norm_num
      have hpow :
          ((1 / 2 : ℝ) / (1 - r) ^ 3) * (fragPermThirdSaddleDeltaReal r) ^ 2 / 2 =
            (1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)) := by
        rw [hδsq_eq]
        rw [show ((1 / 2 : ℝ) / (1 - r) ^ 3) *
              (1 - r) ^ (29 / 10 : ℝ) / 2 =
            (1 / 4 : ℝ) * (((1 - r) ^ 3)⁻¹ *
              (1 - r) ^ (29 / 10 : ℝ)) by ring]
        rw [show (1 - r) ^ 3 = (1 - r) ^ (3 : ℝ) by
          exact (Real.rpow_natCast (1 - r) 3).symm]
        rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
        rw [← Real.rpow_add hu_pos]
        norm_num
      calc
        (1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))
            = ((1 / 2 : ℝ) / (1 - r) ^ 3) *
                (fragPermThirdSaddleDeltaReal r) ^ 2 / 2 := hpow.symm
        _ ≤ fragPermSaddleBReal r * θ ^ 2 / 2 := by
          nlinarith [hB_lower, hθsq, hbpos.le, sq_nonneg θ]
    have hgauss :
        Real.exp (-(fragPermSaddleBReal r * θ ^ 2 / 2)) ≤
          Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hnorm_eq :=
      saddleGAt_norm_eq_gaussian_mul_saddleLocalRatio_norm
        fragPermFun fragPermSaddleAReal fragPermSaddleBReal r n θ
    rw [hnorm_eq]
    unfold fragPermThirdTailE fragPermThirdNearTailE
    calc
      Real.exp (-(fragPermSaddleBReal r * θ ^ 2 / 2)) *
          ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ‖
          ≤ Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))) * 2 :=
            mul_le_mul hgauss hratio_norm (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ 2 * Real.exp (-(1 / 4 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))) +
            fragPermTailE r := by
            have hfar_nonneg : 0 ≤ fragPermTailE r := by
              unfold fragPermTailE
              positivity
            nlinarith
  · have hθold : fragPermSaddleDeltaReal r ≤ |θ| := le_of_not_ge hnear
    have hfar_bound := hfar n θ hθold hθπ
    unfold fragPermThirdTailE
    exact hfar_bound.trans (le_add_of_nonneg_left
      (by unfold fragPermThirdNearTailE; positivity))

lemma fragPerm_tail_third_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in fragPermRadFilter, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r /
          fragPermThirdCorrScale r)
        fragPermRadFilter (𝓝 0) ∧
      (∀ᶠ r : ℝ in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
        fragPermThirdSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt fragPermFun r n θ‖ ≤ E r) := by
  exact ⟨fragPermThirdTailE, fragPermThirdTailE_nonneg_eventually,
    fragPermThirdTailE_decay, fragPerm_third_tail_bound_eventually⟩

private lemma fragPerm_third_gaussian_abs_monomial_integrable (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ k) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    linarith
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

private lemma fragPermThirdLocalDom_nonneg (x : ℝ) :
    0 ≤ fragPermThirdLocalDom x := by
  unfold fragPermThirdLocalDom
  positivity

private lemma fragPermThirdLocalDom_integrable : Integrable fragPermThirdLocalDom := by
  have hterms :
      ∀ k ∈ Finset.range 36,
        Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ k) := by
    intro k hk
    exact fragPerm_third_gaussian_abs_monomial_integrable k
  have hsum :
      Integrable
        (fun x : ℝ =>
          ∑ k ∈ Finset.range 36, Real.exp (-(x ^ 2) / 2) * |x| ^ k) :=
    integrable_finset_sum (Finset.range 36) hterms
  convert hsum using 1
  ext x
  unfold fragPermThirdLocalDom
  rw [Finset.mul_sum]

private lemma fragPermThirdLocalDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, fragPermThirdLocalDom x :=
  integral_nonneg (fun x => fragPermThirdLocalDom_nonneg x)

private lemma fragPermThirdLocalDom_continuous : Continuous fragPermThirdLocalDom := by
  unfold fragPermThirdLocalDom
  fun_prop

private lemma fragPermThirdLocalDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, fragPermThirdLocalDom x) ≤ ∫ x : ℝ, fragPermThirdLocalDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral fragPermThirdLocalDom_integrable
    (Eventually.of_forall fragPermThirdLocalDom_nonneg)

private lemma fragPermThirdLocalL1Const_pos : 0 < fragPermThirdLocalL1Const := by
  unfold fragPermThirdLocalL1Const fragPermThirdScaledRemainderConst
  positivity

/-- The same fragmented-permutation H-admissible data, but with the narrower
third-order finite-radius window. -/
def fragPermThirdWindowHAdmissible : HAdmissible fragPermFun fragPermSeries where
  ρ := (1 : ℝ≥0∞)
  radFilter := fragPermRadFilter
  a := fragPermSaddleAReal
  b := fragPermSaddleBReal
  δ := fragPermThirdSaddleDeltaReal
  hp := fragPermFun_hasFPowerSeriesAt_zero
  radius_eq := fragPermSeries_radius_eq_one
  radius_pos := by norm_num
  rad_neBot := fragPermRadFilter_neBot
  r_pos := fragPerm_r_pos_eventually
  differentiableOn := fragPerm_differentiableOn_eventually
  f_pos := fragPerm_f_pos_eventually
  b_pos := fragPerm_b_pos_eventually
  δ_pos := fragPerm_third_delta_pos_eventually
  δ_le_pi := fragPerm_third_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := fragPerm_third_delta_sqrt_b_tendsto_atTop
  local_uniform := by
    intro ε hε
    have hlocal := fragPerm_hayman_uniform_estimates.1 ε hε
    filter_upwards [hlocal, fragPerm_third_delta_le_second_delta_eventually] with
      r hloc hδle θ hθ
    exact hloc θ (hθ.trans hδle)
  tail_uniform := by
    rcases fragPerm_tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
    refine ⟨E, hE_nonneg, ?_, htail⟩
    have hprod := hdecay.mul fragPermThirdCorrScale_tendsto_zero
    have hprod0 :
        Tendsto
          (fun r : ℝ =>
            Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r /
              fragPermThirdCorrScale r * fragPermThirdCorrScale r)
          fragPermRadFilter (𝓝 0) := by
      simpa using hprod
    refine Tendsto.congr' ?_ hprod0
    filter_upwards [fragPermThirdCorrScale_pos_eventually] with r hpos
    field_simp [hpos.ne']

def fragPermThirdWindowSaddleSequence :
    SaddleSequence fragPermThirdWindowHAdmissible where
  r := fragPermSaddleRadius
  tendsTo := by
    simpa [fragPermThirdWindowHAdmissible] using fragPermSaddleRadius_tendsto_radFilter
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change fragPermSaddleAReal (fragPermSaddleRadius n) = (n : ℝ)
      exact fragPermSaddleAReal_radius n

private lemma fragPerm_third_local_integrand_continuous (r : ℝ)
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
            fragPermSaddleB5Real fragPermSaddleB6Real r x)‖ := by
  have hr0 : 0 ≤ r := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1).le
  have hden_circle :
      ∀ x : ℝ,
        1 - (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hzero
    have hz :
        (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    have hexp_norm :
        ‖Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hnorm_left :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = r := by
      have hr_norm : ‖(r : ℂ)‖ = r :=
        (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_nonneg hr0)
      rw [norm_mul, hr_norm, hexp_norm, mul_one]
    have hnorm_one :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [hz]
      norm_num
    linarith [hr.2]
  have hden_real : (1 : ℂ) - (r : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith [hr.2]
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))) -
            saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
              fragPermSaddleB5Real fragPermSaddleB6Real r x)‖ := by
    have hzcont :
        Continuous fun x : ℝ =>
          (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hfragCircle :
        Continuous fun x : ℝ =>
          fragPermH ((r : ℂ) *
            Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)) := by
      unfold fragPermH
      exact hzcont.div (continuous_const.sub hzcont) hden_circle
    have hlin :
        Continuous fun x : ℝ =>
          ((fragPermSaddleAReal r * (x / Real.sqrt (fragPermSaddleBReal r)) : ℝ) : ℂ) *
            Complex.I := by
      fun_prop
    have hquad :
        Continuous fun x : ℝ =>
          ((fragPermSaddleBReal r * (x / Real.sqrt (fragPermSaddleBReal r)) ^ 2 / 2 : ℝ) : ℂ) := by
      fun_prop
    have hlocal :
        Continuous fun x : ℝ =>
          fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) := by
      unfold fragPermLocalExponent
      exact ((hfragCircle.sub continuous_const).sub hlin).add hquad
    have hsaddle :
        Continuous fun x : ℝ =>
          saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
            fragPermSaddleB5Real fragPermSaddleB6Real r x := by
      unfold saddleThirdPoly saddleSecondPoly
      fun_prop
    have hgauss : Continuous fun x : ℝ => Complex.exp (-(x ^ 2) / 2) := by
      fun_prop
    exact (hgauss.mul ((Complex.continuous_exp.comp hlocal).sub hsaddle)).norm
  simpa [fragPerm_saddleLocalRatio_eq] using h

private lemma fragPerm_second_local_integrand_continuous (r : ℝ)
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖ := by
  have hr0 : 0 ≤ r := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1).le
  have hden_circle :
      ∀ x : ℝ,
        1 - (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x hzero
    have hz :
        (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) = 1 := by
      exact (sub_eq_zero.mp hzero).symm
    have hexp_norm :
        ‖Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hnorm_left :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = r := by
      have hr_norm : ‖(r : ℂ)‖ = r :=
        (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_nonneg hr0)
      rw [norm_mul, hr_norm, hexp_norm, mul_one]
    have hnorm_one :
        ‖(r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [hz]
      norm_num
    linarith [hr.2]
  have hden_real : (1 : ℂ) - (r : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith [hr.2]
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))) -
            saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖ := by
    have hzcont :
        Continuous fun x : ℝ =>
          (r : ℂ) * Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I) := by
      fun_prop
    have hfragCircle :
        Continuous fun x : ℝ =>
          fragPermH ((r : ℂ) *
            Complex.exp (((x / Real.sqrt (fragPermSaddleBReal r) : ℝ) : ℂ) * Complex.I)) := by
      unfold fragPermH
      exact hzcont.div (continuous_const.sub hzcont) hden_circle
    have hlin :
        Continuous fun x : ℝ =>
          ((fragPermSaddleAReal r * (x / Real.sqrt (fragPermSaddleBReal r)) : ℝ) : ℂ) *
            Complex.I := by
      fun_prop
    have hquad :
        Continuous fun x : ℝ =>
          ((fragPermSaddleBReal r * (x / Real.sqrt (fragPermSaddleBReal r)) ^ 2 / 2 : ℝ) : ℂ) := by
      fun_prop
    have hlocal :
        Continuous fun x : ℝ =>
          fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r)) := by
      unfold fragPermLocalExponent
      exact ((hfragCircle.sub continuous_const).sub hlin).add hquad
    have hsaddle :
        Continuous fun x : ℝ =>
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x := by
      unfold saddleSecondPoly
      fun_prop
    have hgauss : Continuous fun x : ℝ => Complex.exp (-(x ^ 2) / 2) := by
      fun_prop
    exact (hgauss.mul ((Complex.continuous_exp.comp hlocal).sub hsaddle)).norm
  simpa [fragPerm_saddleLocalRatio_eq] using h

private lemma fragPermThirdCorrScale_div_secondCorrScale_tendsto_zero :
    Tendsto
      (fun r : ℝ => fragPermThirdCorrScale r / fragPermSecondCorrScale r)
      fragPermRadFilter (𝓝 0) := by
  have hone :
      Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
    fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  refine Tendsto.congr' ?_ hone
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermThirdCorrScale fragPermSecondCorrScale
  have hu : 1 - r ≠ 0 := by linarith [hr.2]
  field_simp [hu]

lemma fragPerm_thirdWindow_local_second_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real r x)‖) /
            fragPermSecondCorrScale r)
        fragPermRadFilter (𝓝 0) := by
  have hwide := fragPerm_local_second_L1
  refine squeeze_zero' ?_ ?_ hwide
  · filter_upwards [fragPerm_eventually_Ioo_zero_one, fragPermSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, fragPermThirdSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [fragPerm_eventually_Ioo_half_one,
      fragPerm_third_delta_le_second_delta_eventually,
      fragPermSecondCorrScale_pos_eventually] with r hr hδle hcorr
    let L3 : ℝ := fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    let L2 : ℝ := fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleSecondPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real r x)‖
    have hsqrt_nonneg : 0 ≤ Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_nonneg _
    have hL3nonneg : 0 ≤ L3 := by
      dsimp [L3, fragPermThirdSaddleDeltaReal]
      positivity
    have hL2nonneg : 0 ≤ L2 := by
      dsimp [L2, fragPermSaddleDeltaReal]
      positivity
    have hLle : L3 ≤ L2 := by
      dsimp [L3, L2]
      exact mul_le_mul_of_nonneg_right hδle hsqrt_nonneg
    have hsmall_le_big_left : -L2 ≤ -L3 := by linarith
    have hsmall_le_big_right : L3 ≤ L2 := hLle
    have hsmall_order : -L3 ≤ L3 := by linarith
    have hFnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (-L2) L2)] F :=
      Eventually.of_forall fun x => norm_nonneg _
    have hFint : IntervalIntegrable F volume (-L2) L2 := by
      exact (fragPerm_second_local_integrand_continuous r hr).intervalIntegrable _ _
    have hInt :
        (∫ x in -L3..L3, F x) ≤ ∫ x in -L2..L2, F x :=
      intervalIntegral.integral_mono_interval hsmall_le_big_left hsmall_order
        hsmall_le_big_right hFnonneg hFint
    have hdiv :
        (∫ x in -L3..L3, F x) / fragPermSecondCorrScale r ≤
          (∫ x in -L2..L2, F x) / fragPermSecondCorrScale r :=
      div_le_div_of_nonneg_right hInt hcorr.le
    simpa [L3, L2, F] using hdiv

def fragPermThirdWindowSecondOrder :
    SecondOrderHAdmissible fragPermThirdWindowHAdmissible where
  b3 := fragPermSaddleB3Real
  b4 := fragPermSaddleB4Real
  corrScale := fragPermSecondCorrScale
  corrScale_pos := by
    simpa [fragPermThirdWindowHAdmissible] using fragPermSecondCorrScale_pos_eventually
  corrScale_tendsto_zero := by
    simpa [fragPermThirdWindowHAdmissible] using fragPermSecondCorrScale_tendsto_zero
  corrScale_dominates_correction := by
    refine ⟨200, by norm_num, ?_⟩
    simpa [fragPermThirdWindowHAdmissible] using
      fragPerm_saddleCorrectionScale_le_oneSub_eventually
  local_second_L1 := by
    simpa [fragPermThirdWindowHAdmissible] using fragPerm_thirdWindow_local_second_L1
  tail_second_uniform := by
    rcases fragPerm_tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
    refine ⟨E, ?_, ?_, ?_⟩
    · simpa [fragPermThirdWindowHAdmissible] using hE_nonneg
    · have hprod := hdecay.mul fragPermThirdCorrScale_div_secondCorrScale_tendsto_zero
      have hprod0 :
          Tendsto
            (fun r : ℝ =>
              Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r /
                fragPermThirdCorrScale r *
                  (fragPermThirdCorrScale r / fragPermSecondCorrScale r))
            fragPermRadFilter (𝓝 0) := by
        simpa using hprod
      refine Tendsto.congr' ?_ hprod0
      filter_upwards [fragPermThirdCorrScale_pos_eventually,
        fragPermSecondCorrScale_pos_eventually] with r hthird hsecond
      field_simp [hthird.ne', hsecond.ne']
      simp [fragPermThirdWindowHAdmissible, mul_comm, mul_left_comm, mul_assoc]
    · simpa [fragPermThirdWindowHAdmissible] using htail

theorem fragPerm_thirdWindow_local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖) /
            fragPermThirdCorrScale r)
        fragPermRadFilter (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, fragPermThirdLocalDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact fragPermThirdLocalDom_integral_nonneg
  have hpow_tendsto :
      Tendsto (fun r : ℝ => (1 - r) ^ (1 / 2 : ℝ))
        fragPermRadFilter (𝓝 0) := by
    have hu :
        Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
      fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
    simpa [Function.comp_def] using
      ((Real.continuousAt_rpow_const (0 : ℝ) (1 / 2 : ℝ)
        (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))).tendsto.comp hu)
  have hupper_tendsto :
      Tendsto
        (fun r : ℝ => fragPermThirdLocalL1Const * M * (1 - r) ^ (1 / 2 : ℝ))
        fragPermRadFilter (𝓝 0) := by
    simpa [mul_assoc] using hpow_tendsto.const_mul (fragPermThirdLocalL1Const * M)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [fragPerm_eventually_Ioo_zero_one, fragPermThirdCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      exact mul_nonneg
        (by
          unfold fragPermThirdSaddleDeltaReal
          exact Real.rpow_nonneg (by linarith [hr.2] : 0 ≤ 1 - r) _)
        (Real.sqrt_nonneg _)
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [fragPerm_eventually_Ioo_half_one,
      fragPerm_third_delta_le_one_eventually,
      fragPerm_third_delta_le_one_sub_quarter_eventually,
      fragPerm_third_delta_le_second_delta_eventually,
      fragPerm_delta_le_one_eventually,
      fragPerm_delta_le_one_sub_quarter_eventually,
      fragPermLocalBound_tendsto_zero.eventually_le_const zero_lt_one,
      fragPermThirdCorrScale_pos_eventually] with
      r hr hδ3le hδ3u hδ32 hδ2le hδ2u hlocSmall hcorrPos
    let L : ℝ := fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
            (x / Real.sqrt (fragPermSaddleBReal r)) -
          saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real fragPermSaddleB4Real
            fragPermSaddleB5Real fragPermSaddleB6Real r x)‖
    let H : ℝ → ℝ := fun x =>
      (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * fragPermThirdLocalDom x
    have hbpos : 0 < fragPermSaddleBReal r := by
      unfold fragPermSaddleBReal
      have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1
      have hnum : 0 < r * (1 + r) := mul_pos hrpos (by linarith)
      have hden : 0 < (1 - r) ^ 3 := pow_pos (by linarith [hr.2] : 0 < 1 - r) _
      exact div_pos hnum hden
    have hsqrt_pos : 0 < Real.sqrt (fragPermSaddleBReal r) := Real.sqrt_pos.mpr hbpos
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      exact mul_nonneg
        (by
          unfold fragPermThirdSaddleDeltaReal
          exact Real.rpow_nonneg (by linarith [hr.2] : 0 ≤ 1 - r) _)
        (Real.sqrt_nonneg _)
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ H x := by
      intro x hx
      have hxabs : |x| ≤ L := by
        exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hθδ3 : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermThirdSaddleDeltaReal r := by
        rw [abs_div, abs_of_pos hsqrt_pos]
        calc
          |x| / Real.sqrt (fragPermSaddleBReal r) ≤
              L / Real.sqrt (fragPermSaddleBReal r) :=
            div_le_div_of_nonneg_right hxabs hsqrt_pos.le
          _ = fragPermThirdSaddleDeltaReal r := by
            dsimp [L]
            exact mul_div_cancel_right₀ (fragPermThirdSaddleDeltaReal r) hsqrt_pos.ne'
      have hθδ2 : |x / Real.sqrt (fragPermSaddleBReal r)| ≤ fragPermSaddleDeltaReal r :=
        hθδ3.trans hδ32
      have hWnorm :
          ‖fragPermLocalExponent r (x / Real.sqrt (fragPermSaddleBReal r))‖ ≤ 1 :=
        (fragPerm_local_exponent_norm_le
          (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr.1).le hr.2
          hδ2le hδ2u hθδ2).trans hlocSmall
      have hb := fragPerm_third_local_integrand_bound hr hθδ3 hδ3le hδ3u hWnorm
      dsimp [F, H]
      exact hb
    have hFint : IntervalIntegrable F volume (-L) L := by
      exact (fragPerm_third_local_integrand_continuous r hr).intervalIntegrable _ _
    have hHint : IntervalIntegrable H volume (-L) L := by
      exact (fragPermThirdLocalDom_continuous.const_mul
        (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ))).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤
          (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M := by
      have hconst_nonneg :
          0 ≤ fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ) := by
        exact mul_nonneg fragPermThirdLocalL1Const_pos.le
          (Real.rpow_nonneg (by linarith [hr.2] : 0 ≤ 1 - r) _)
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, H x :=
          intervalIntegral.integral_mono_on hle hFint hHint hpoint
        _ = (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) *
              (∫ x in -L..L, fragPermThirdLocalDom x) := by
          dsimp [H]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact fragPermThirdLocalDom_window_le_integral hLnonneg)
            hconst_nonneg
    have hmain :
        (∫ x in -L..L, F x) / fragPermThirdCorrScale r ≤
          ((fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M) /
            fragPermThirdCorrScale r := by
      exact div_le_div_of_nonneg_right hIntBound hcorrPos.le
    have hu_pos : 0 < 1 - r := by linarith [hr.2]
    have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
    have hratio :
        (1 - r) ^ (5 / 2 : ℝ) / (1 - r) ^ 2 =
          (1 - r) ^ (1 / 2 : ℝ) := by
      rw [show (1 - r) ^ 2 = (1 - r) ^ (2 : ℝ) by
        exact (Real.rpow_natCast (1 - r) 2).symm]
      rw [div_eq_mul_inv, ← Real.rpow_neg hu_nonneg (2 : ℝ),
        ← Real.rpow_add hu_pos]
      norm_num
    calc
      ((∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖) /
          fragPermThirdCorrScale r)
          = (∫ x in -L..L, F x) / fragPermThirdCorrScale r := by rfl
      _ ≤ ((fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M) /
            fragPermThirdCorrScale r := hmain
      _ = fragPermThirdLocalL1Const * M * (1 - r) ^ (1 / 2 : ℝ) := by
        unfold fragPermThirdCorrScale
        calc
          ((fragPermThirdLocalL1Const * (1 - r) ^ (5 / 2 : ℝ)) * M) /
              (1 - r) ^ 2
              = fragPermThirdLocalL1Const * M *
                  ((1 - r) ^ (5 / 2 : ℝ) / (1 - r) ^ 2) := by
                field_simp [(pow_pos hu_pos 2).ne']
          _ = fragPermThirdLocalL1Const * M * (1 - r) ^ (1 / 2 : ℝ) := by
            rw [hratio]

theorem fragPerm_thirdWindow_local_third_L1_robust :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
          (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                (x / Real.sqrt (fragPermSaddleBReal r)) -
              saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖) /
            fragPermThirdRobustCorrScale r)
        fragPermRadFilter (𝓝 0) := by
  have htrue := fragPerm_thirdWindow_local_third_L1
  have hratio := fragPermThirdCorrScale_div_secondCorrScale_tendsto_zero
  have hprod := htrue.mul hratio
  have hprod0 :
      Tendsto
        (fun r : ℝ =>
          ((∫ x in -(fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r))..
            (fragPermThirdSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r)),
            ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r
                  (x / Real.sqrt (fragPermSaddleBReal r)) -
                saddleThirdPoly fragPermSaddleBReal fragPermSaddleB3Real
                  fragPermSaddleB4Real fragPermSaddleB5Real fragPermSaddleB6Real r x)‖) /
              fragPermThirdCorrScale r) *
            (fragPermThirdCorrScale r / fragPermSecondCorrScale r))
        fragPermRadFilter (𝓝 0) := by
    simpa using hprod
  refine Tendsto.congr' ?_ hprod0
  filter_upwards [fragPermThirdCorrScale_pos_eventually,
    fragPermSecondCorrScale_pos_eventually] with r hthird hsecond
  field_simp [fragPermThirdRobustCorrScale, hthird.ne', hsecond.ne']
  simp [fragPermThirdRobustCorrScale, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

def fragPermThirdWindowThirdOrder :
    ThirdOrderHAdmissible fragPermThirdWindowHAdmissible fragPermThirdWindowSecondOrder where
  b5 := fragPermSaddleB5Real
  b6 := fragPermSaddleB6Real
  corrScale3 := fragPermThirdRobustCorrScale
  corrScale3_pos := by
    simpa [fragPermThirdWindowHAdmissible, fragPermThirdRobustCorrScale] using
      fragPermSecondCorrScale_pos_eventually
  corrScale3_tendsto_zero := by
    simpa [fragPermThirdWindowHAdmissible, fragPermThirdRobustCorrScale] using
      fragPermSecondCorrScale_tendsto_zero
  corrScale3_dominates_correction := by
    rcases fragPerm_saddleThirdCorrectionScale_le_sq_eventually with
      ⟨K3, hK3nonneg, hK3⟩
    refine ⟨200 + K3, by positivity, ?_⟩
    filter_upwards [fragPerm_saddleCorrectionScale_le_oneSub_eventually, hK3,
      fragPerm_eventually_Ioo_zero_one] with r hsecond hpure hr
    have hthird_le_second : fragPermThirdCorrScale r ≤ fragPermSecondCorrScale r := by
      unfold fragPermThirdCorrScale fragPermSecondCorrScale
      have hu_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
      have hu_le_one : 1 - r ≤ 1 := by linarith [hr.1]
      nlinarith [sq_nonneg (1 - r)]
    have hpure_second :
        |fragPermSaddleB6Real r| / (fragPermSaddleBReal r) ^ 3
          + |fragPermSaddleB3Real r * fragPermSaddleB5Real r| /
              (fragPermSaddleBReal r) ^ 4
          + (fragPermSaddleB4Real r) ^ 2 / (fragPermSaddleBReal r) ^ 4
          + (fragPermSaddleB3Real r) ^ 2 * |fragPermSaddleB4Real r| /
              (fragPermSaddleBReal r) ^ 5
          + (fragPermSaddleB3Real r) ^ 4 / (fragPermSaddleBReal r) ^ 6
            ≤ K3 * fragPermSecondCorrScale r :=
      hpure.trans (mul_le_mul_of_nonneg_left hthird_le_second hK3nonneg)
    have hsecond_exp := hsecond
    simp only [saddleCorrectionScale, fragPermSaddleBReal] at hsecond_exp
    have hpure_second_exp := hpure_second
    simp only [fragPermSaddleBReal] at hpure_second_exp
    rw [saddleThirdCorrectionScale_apply]
    dsimp [fragPermThirdWindowHAdmissible, fragPermThirdWindowSecondOrder,
      fragPermThirdRobustCorrScale]
    nlinarith [hsecond_exp, hpure_second_exp]
  local_third_L1 := by
    simpa [fragPermThirdWindowHAdmissible, fragPermThirdWindowSecondOrder,
      fragPermThirdRobustCorrScale] using
      fragPerm_thirdWindow_local_third_L1_robust
  tail_third_uniform := by
    rcases fragPerm_tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
    refine ⟨E, ?_, ?_, ?_⟩
    · simpa [fragPermThirdWindowHAdmissible] using hE_nonneg
    · have hprod := hdecay.mul fragPermThirdCorrScale_div_secondCorrScale_tendsto_zero
      have hprod0 :
          Tendsto
            (fun r : ℝ =>
              Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r /
                fragPermThirdCorrScale r *
                  (fragPermThirdCorrScale r / fragPermSecondCorrScale r))
            fragPermRadFilter (𝓝 0) := by
        simpa using hprod
      refine Tendsto.congr' ?_ hprod0
      filter_upwards [fragPermThirdCorrScale_pos_eventually,
        fragPermSecondCorrScale_pos_eventually] with r hthird hsecond
      field_simp [fragPermThirdWindowHAdmissible, fragPermThirdRobustCorrScale,
        hthird.ne', hsecond.ne']
      simp [fragPermThirdWindowHAdmissible, fragPermThirdRobustCorrScale,
        mul_comm, mul_left_comm, mul_assoc]
    · simpa [fragPermThirdWindowHAdmissible] using htail

theorem fragPerm_coeff_thirdOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      fragPermThirdOrderSeriesError n)
      =o[atTop]
    (fun n : ℕ => (fragPermThirdRobustCorrScale (fragPermSaddleRadius n) : ℂ)) := by
  have h :=
    coeff_thirdOrder_saddle
      fragPermThirdWindowHAdmissible fragPermThirdWindowSecondOrder
      fragPermThirdWindowThirdOrder fragPermThirdWindowSaddleSequence
  simpa [fragPermThirdOrderSeriesError, fragPermThirdOrderSaddleScale,
    fragPermSecondCorrectionAtSaddle, fragPermThirdCorrectionAtSaddle,
    HAdmissible.B, fragPermThirdWindowHAdmissible,
    fragPermThirdWindowSaddleSequence, fragPermThirdWindowSecondOrder,
    fragPermThirdWindowThirdOrder, fragPermThirdRobustCorrScale] using h

end FragmentedPermHAdmissible
end

open FragmentedPermHAdmissible
open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
theorem solution :
    (fun n : ℕ =>
      fragPermSeries.coeff n / fragPermThirdOrderSaddleScale n -
        (1 + (fragPermSecondCorrectionAtSaddle n : ℂ) +
          (fragPermThirdCorrectionAtSaddle n : ℂ)))
      =o[atTop]
    (fun n : ℕ => (fragPermThirdRobustCorrScale (fragPermSaddleRadius n) : ℂ)) := by
  simpa [fragPermThirdOrderSeriesError] using
    fragPerm_coeff_thirdOrder_saddle_from_HAdmissible
