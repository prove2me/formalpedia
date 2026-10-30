-- Prove2me | solution 1 for InvolutionHAdmissible.involution_count_over_factorial_thirdOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T00:25:11.461067+00:00
-- url     : https://prove2.me/submissions/e6a621b0-0342-4eec-ab7b-7496e946ab85

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Exp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bell
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionThirdOrder
import Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_egf_set
import Theorems.Thm_coeff_thirdOrder_saddle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Probability.Distributions.Gaussian.Real
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
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
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
/-!
# Ch1 §I.3 — Fibonacci numbers as compositions into parts `1` and `2`

Flajolet & Sedgewick, Part A, Chapter I, §I.3. Let `D` be the class with one
object of size `1` and one of size `2`. Then `SEQ(D)` enumerates compositions of
`n` into parts of size `1` and `2`, and

* `counts_seq_parts12` — there are `F_{n+1}` of them (`Nat.fib (n+1)`), via the
  convolution recursion `counts_seq_succ`, which here is the Fibonacci recurrence;
* `ogf_parts12` / `ogf_seq_parts12` — `D(z) = z + z²` and the OGF is
  `1/(1 - z - z²)`, the Fibonacci generating function.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.counts_parts12 (n : ℕ) :
    CombClass.parts12.counts n = if n = 1 then 1 else if n = 2 then 1 else 0 :=
  Fintype.card_fin _

end AnalyticCombinatorics.Ch1
end

section
/-!
# Ch2 §II.3 — Applications of the labelled symbolic method

Flajolet & Sedgewick, Part A, Chapter II, §II.3. Using the labelled set and
sequence transfers on the positive-integer ("urn"/nonempty-block) class `ℙ`
(one object of each size `n ≥ 1`, EGF `e^z - 1`):

* set partitions / **Bell numbers** `SET(ℙ)`, EGF `exp(e^z - 1)`;
* **surjections** `SEQ(ℙ)`, EGF `1/(2 - e^z)`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The EGF of the "singletons-and-pairs" class is `z + z²/2`. -/
theorem CombClass.egf_parts12_egf :
    CombClass.parts12.egf = X + (2⁻¹ : ℚ) • X ^ 2 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_parts12, map_add, coeff_X, map_smul, coeff_X_pow,
    smul_eq_mul]
  rcases n with _ | _ | _ | m <;> norm_num [Nat.factorial] <;> omega

/-- **Involutions** (F&S §II.3): an involution is a set of fixed points and
transpositions, `SET(ℙ₁₂)` where `ℙ₁₂` has one object each of size 1 and 2.
Its EGF is `exp(z + z²/2)`. -/
theorem CombClass.egf_involutions :
    CombClass.parts12.set.egf = (PowerSeries.exp ℚ).subst (X + (2⁻¹ : ℚ) • X ^ 2) := by
  rw [CombClass.egf_set _ (by simp [CombClass.counts_parts12]), CombClass.egf_parts12_egf]

end AnalyticCombinatorics.Ch1
end

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
open Complex
open scoped NNReal ENNReal

noncomputable section

theorem coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi * I : ℂ)⁻¹ •
        circleIntegral
          (fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z)
          0 R := by
  have hq : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R) 0 := by
    have hnn : 0 < ((⟨R, hR.le⟩ : ℝ≥0)) := by
      exact_mod_cast hR
    exact (hd.hasFPowerSeriesOnBall hnn).hasFPowerSeriesAt
  have hpq : p = cauchyPowerSeries f 0 R := hp.eq_formalMultilinearSeries hq
  calc
    p.coeff n = (cauchyPowerSeries f 0 R).coeff n := by rw [hpq]
    _ = (cauchyPowerSeries f 0 R n fun _ => (1 : ℂ)) := by rfl
    _ = _ := by exact cauchyPowerSeries_apply f 0 R n 1

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
/-!
# Saddle-point assembly bricks

This file contains the exact Cauchy parameterization on `[-pi, pi]` and the
bounded algebraic assembly theorem for a central/tail saddle decomposition.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal

noncomputable section

private lemma saddlePhase_periodic (n : ℕ) :
    Function.Periodic (fun θ : ℝ => Complex.exp (-(↑↑n * ↑θ) * Complex.I))
      (2 * Real.pi) := by
  intro θ
  change Complex.exp (-(↑↑n * ↑(θ + 2 * Real.pi)) * Complex.I) =
    Complex.exp (-(↑↑n * ↑θ) * Complex.I)
  rw [show -(↑↑n * ↑(θ + 2 * Real.pi)) * I =
      -(↑↑n * ↑θ) * I - ↑n * (2 * ↑Real.pi * I) by
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    norm_num
    ring_nf]
  exact Complex.exp_periodic.sub_nat_mul_eq n

private lemma saddleRawIntegrand_periodic (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    Function.Periodic (saddleRawIntegrand f r n) (2 * Real.pi) := by
  have hcircle0 :
      Function.Periodic (fun θ : ℝ => f (circleMap (0 : ℂ) r θ)) (2 * Real.pi) :=
    (periodic_circleMap (0 : ℂ) r).comp f
  have hcircle :
      Function.Periodic
        (fun θ : ℝ => f ((r : ℂ) * Complex.exp (θ * Complex.I))) (2 * Real.pi) := by
    simpa [circleMap_zero] using hcircle0
  exact hcircle.mul (saddlePhase_periodic n)

private lemma saddleRawIntegral_zero_to_neg_pi (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ) =
      ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
  have h := (saddleRawIntegrand_periodic f r n).intervalIntegral_add_eq (-Real.pi) 0
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using h.symm

private lemma cauchyCircleIntegrand_param_eq
    (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (n : ℕ) (θ : ℝ) :
    deriv (circleMap (0 : ℂ) r) θ •
      (((1 : ℂ) / (circleMap (0 : ℂ) r θ - 0)) ^ n •
        (circleMap (0 : ℂ) r θ - 0)⁻¹ • f (circleMap (0 : ℂ) r θ)) =
    Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcircle : deriv (circleMap (0 : ℂ) r) θ =
      circleMap (0 : ℂ) r θ * Complex.I :=
    _root_.deriv_circleMap (0 : ℂ) r θ
  rw [hcircle]
  simp [saddleRawIntegrand, circleMap_zero, smul_eq_mul, div_eq_mul_inv,
    mul_pow, Complex.exp_neg, mul_comm, mul_left_comm, mul_assoc]
  field_simp [hrC, Complex.exp_ne_zero]
  rw [← Complex.exp_nat_mul]
  ring_nf

private lemma two_pi_I_inv_mul_I :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) = (2 * Real.pi : ℂ)⁻¹ := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have htwo : (2 * Real.pi : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  field_simp [hI, htwo]

/-- Cauchy's coefficient formula parameterized on the interval `[-pi, pi]`. -/
theorem coeff_eq_saddle_param
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi : ℂ)⁻¹ * (r : ℂ)⁻¹ ^ n *
        ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
  set_option backward.isDefEq.respectTransparency false in
    have hc := coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt hr hp hd n
    rw [hc]
    rw [circleIntegral]
    have hcongr :
        (∫ θ in (0 : ℝ)..2 * Real.pi,
            deriv (circleMap (0 : ℂ) r) θ •
              (((1 : ℂ) / (circleMap (0 : ℂ) r θ - 0)) ^ n •
                (circleMap (0 : ℂ) r θ - 0)⁻¹ • f (circleMap (0 : ℂ) r θ))) =
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact cauchyCircleIntegrand_param_eq f hr n θ
    rw [hcongr]
    rw [show (∫ θ in (0 : ℝ)..2 * Real.pi,
            Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) =
          Complex.I * ((r : ℂ)⁻¹ ^ n) *
            ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ by
      calc
        (∫ θ in (0 : ℝ)..2 * Real.pi,
            Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ)
            = ∫ θ in (0 : ℝ)..2 * Real.pi,
                Complex.I * (((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) := by
              apply intervalIntegral.integral_congr
              intro θ _
              ring
        _ = Complex.I *
              (∫ θ in (0 : ℝ)..2 * Real.pi,
                ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) := by
              exact intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 2 * Real.pi)
                (μ := MeasureTheory.volume) (r := Complex.I)
                (f := fun θ => ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ)
        _ = Complex.I * (((r : ℂ)⁻¹ ^ n) *
              ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ) := by
              exact congrArg (fun z : ℂ => Complex.I * z)
                (intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 2 * Real.pi)
                  (μ := MeasureTheory.volume) (r := ((r : ℂ)⁻¹ ^ n))
                  (f := fun θ => saddleRawIntegrand f r n θ))
        _ = Complex.I * ((r : ℂ)⁻¹ ^ n) *
              ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ := by
              ring]
    rw [saddleRawIntegral_zero_to_neg_pi]
    calc
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (Complex.I * ((r : ℂ)⁻¹ ^ n) *
            ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ)
          =
            ((((2 * Real.pi : ℂ) * Complex.I)⁻¹) * Complex.I) *
              ((r : ℂ)⁻¹ ^ n) *
                ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
              simp [smul_eq_mul]
              ring
      _ = (2 * Real.pi : ℂ)⁻¹ * (r : ℂ)⁻¹ ^ n *
            ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
              rw [two_pi_I_inv_mul_I]

private lemma saddleRawIntegrand_eq_const_mul_saddleGAt
    (f : ℂ → ℂ) {r : ℝ} (hfnz : f (r : ℂ) ≠ 0) (n : ℕ) (θ : ℝ) :
    saddleRawIntegrand f r n θ = f (r : ℂ) * saddleGAt f r n θ := by
  simp [saddleRawIntegrand, saddleGAt, div_eq_mul_inv, mul_comm, mul_assoc]
  field_simp [hfnz]

/-- Cauchy's parameterization in normalized saddle-integral form. -/
theorem coeff_eq_saddle_param_normalized
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r))
    (hfnz : f (r : ℂ) ≠ 0) (n : ℕ) :
    p.coeff n = saddlePrefAt f r n * saddleJfullAt f r n := by
  rw [coeff_eq_saddle_param hr hp hd n]
  have hraw :
      (∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ) =
        f (r : ℂ) * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ := by
    calc
      (∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ)
          = ∫ θ in (-Real.pi)..Real.pi, f (r : ℂ) * saddleGAt f r n θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            exact saddleRawIntegrand_eq_const_mul_saddleGAt f hfnz n θ
      _ = f (r : ℂ) * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ := by
            exact intervalIntegral.integral_const_mul (a := -Real.pi) (b := Real.pi)
              (μ := MeasureTheory.volume) (r := f (r : ℂ)) (f := fun θ => saddleGAt f r n θ)
  rw [hraw]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [saddlePrefAt, saddleJfullAt]
  field_simp [hrC]

/-- Split the full normalized integral into central and tail pieces. -/
theorem saddleJfullAt_eq_saddleJcAt_add_saddleJtAt
    (f : ℂ → ℂ) (r δ : ℝ) (n : ℕ)
    (hleft : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-Real.pi) (-δ))
    (hcenter : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-δ) δ)
    (hright : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume δ Real.pi) :
    saddleJfullAt f r n = saddleJcAt f r δ n + saddleJtAt f r δ n := by
  have h12 := intervalIntegral.integral_add_adjacent_intervals hleft hcenter
  have hfull := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hcenter) hright
  unfold saddleJfullAt saddleJcAt saddleJtAt
  rw [← hfull, ← h12]
  ring

/-- Exact coefficient split into the central window and the two tails. -/
theorem coeff_eq_saddle_split
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r δ : ℝ} {n : ℕ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r))
    (hfnz : f (r : ℂ) ≠ 0)
    (hleft : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-Real.pi) (-δ))
    (hcenter : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-δ) δ)
    (hright : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume δ Real.pi) :
    p.coeff n = saddlePrefAt f r n * (saddleJcAt f r δ n + saddleJtAt f r δ n) := by
  rw [coeff_eq_saddle_param_normalized hr hp hd hfnz n]
  rw [saddleJfullAt_eq_saddleJcAt_add_saddleJtAt f r δ n hleft hcenter hright]

/-- Eventual sequence version of the exact central/tail split. -/
theorem eventually_coeff_eq_saddle_split
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r δ : ℕ → ℝ)
    (hp : HasFPowerSeriesAt f p 0)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ f (Metric.closedBall 0 (r n)))
    (hfnz : ∀ᶠ n in atTop, f (r n : ℂ) ≠ 0)
    (hleft : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-Real.pi) (-(δ n)))
    (hcenter : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-(δ n)) (δ n))
    (hright : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (δ n) Real.pi) :
    ∀ᶠ n in atTop,
      p.coeff n = saddlePref f r n * (saddleJc f r δ n + saddleJt f r δ n) := by
  filter_upwards [hr, hd, hfnz, hleft, hcenter, hright] with
    n hrn hdn hfnzn hleftn hcentern hrightn
  simpa [saddlePref, saddleJc, saddleJt, saddleG] using
    coeff_eq_saddle_split (f := f) (p := p) (r := r n) (δ := δ n) (n := n)
      hrn hp hdn hfnzn hleftn hcentern hrightn

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
# Gaussian central saddle core

This file packages the reusable dominated-convergence core for the central
Gaussian window after the saddle scaling `theta = x / sqrt (B n)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- The normalized Gaussian integral used by the saddle central window. -/
theorem gaussian_integral_half :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2)) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    have hgauss :=
      integral_gaussian_complex (b := (1 / 2 : ℂ))
        (by norm_num : 0 < (Complex.re (1 / 2 : ℂ)))
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2)) =
        (fun x : ℝ => Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2)) by
          funext x
          norm_num
          ring_nf]
    rw [hgauss]
    have hbase : (↑Real.pi / (1 / 2 : ℂ)) = (↑(2 * Real.pi) : ℂ) := by
      norm_num [div_eq_mul_inv]
      ring
    rw [hbase]
    have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hexp]
    rw [← Complex.ofReal_cpow]
    · rw [Complex.ofReal_inj]
      rw [Real.sqrt_eq_rpow]
    · positivity

private lemma saddle_scaled_constant (B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) :
    (Real.sqrt (2 * Real.pi * B n) : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      ((Real.sqrt (B n))⁻¹ : ℂ) =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) := by
  let c : ℝ := Real.sqrt (B n)
  have hc_pos : 0 < c := by simpa [c] using Real.sqrt_pos.mpr hB
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hsqrt2_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt2_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hsqrt2_pos.ne'
  have hsqrt_prod :
      Real.sqrt (2 * Real.pi * B n) = Real.sqrt (2 * Real.pi) * c := by
    rw [show 2 * Real.pi * B n = (2 * Real.pi) * B n by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  have hconstR :
      Real.sqrt (2 * Real.pi * B n) * (2 * Real.pi)⁻¹ * c⁻¹ =
        1 / Real.sqrt (2 * Real.pi) := by
    rw [hsqrt_prod]
    calc
      (Real.sqrt (2 * Real.pi) * c) * (2 * Real.pi)⁻¹ * c⁻¹
          = Real.sqrt (2 * Real.pi) * (2 * Real.pi)⁻¹ := by
            field_simp [hc_ne]
      _ = Real.sqrt (2 * Real.pi) / (2 * Real.pi) := by
            rw [div_eq_mul_inv]
      _ = Real.sqrt (2 * Real.pi) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) := by
            congr 1
            rw [← sq]
            rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      _ = 1 / Real.sqrt (2 * Real.pi) := by
            field_simp [hsqrt2_ne]
  norm_cast

/--
After the scaling `theta = x / sqrt (B n)`, the central saddle integral has
the normalized full Gaussian prefactor.
-/
theorem saddleJc_eq_integral_scaled
    (f : ℂ → ℂ) (r δ B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) :
    (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        ∫ x in -(δ n * Real.sqrt (B n))..(δ n * Real.sqrt (B n)),
          saddleG f r n (x / Real.sqrt (B n)) := by
  let c : ℝ := Real.sqrt (B n)
  have hc_pos : 0 < c := by simpa [c] using Real.sqrt_pos.mpr hB
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hsubst :
      (∫ θ in (-(δ n))..(δ n), saddleG f r n θ) =
        c⁻¹ • ∫ x in -(δ n * c)..(δ n * c), saddleG f r n (x / c) := by
    have h := intervalIntegral.inv_smul_integral_comp_div
      (f := fun θ : ℝ => saddleG f r n θ)
      (a := -(δ n * c)) (b := δ n * c) c
    have hb : δ n * c / c = δ n := by
      exact mul_div_cancel_right₀ (δ n) hc_ne
    have ha : -(δ n * c) / c = -(δ n) := by
      rw [neg_div, hb]
    rw [ha, hb] at h
    exact h.symm
  unfold saddleJc saddleJcAt
  change (Real.sqrt (2 * Real.pi * B n) : ℂ) *
      ((2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-(δ n))..(δ n), saddleG f r n θ) =
    (1 / Real.sqrt (2 * Real.pi) : ℂ) *
      ∫ x in -(δ n * c)..(δ n * c), saddleG f r n (x / c)
  rw [hsubst]
  rw [show ((c⁻¹ : ℝ) •
        ∫ (x : ℝ) in -(δ n * c)..δ n * c, saddleG f r n (x / c)) =
      ((c⁻¹ : ℂ) *
        ∫ (x : ℝ) in -(δ n * c)..δ n * c, saddleG f r n (x / c)) by
        simp]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [show (Real.sqrt (2 * Real.pi * B n) : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      (c⁻¹ : ℂ) = (1 / Real.sqrt (2 * Real.pi) : ℂ) by
        simpa [c] using saddle_scaled_constant B n hB]

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
# H-admissible saddle-point bridge

This file packages the abstract H-admissible hypotheses needed to feed the
central Gaussian core, the tail estimate, and the Cauchy assembly theorem.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

lemma saddleGAt_eq_gaussian_mul_saddleLocalRatio
    (f : ℂ → ℂ) (a b : ℝ → ℝ) (r x : ℝ) (n : ℕ)
    (hb : 0 < b r) (ha : a r = (n : ℝ)) :
    saddleGAt f r n (x / Real.sqrt (b r)) =
      Complex.exp (-(x ^ 2) / 2) *
        saddleLocalRatio f a b r (x / Real.sqrt (b r)) := by
  let θ : ℝ := x / Real.sqrt (b r)
  have hsqrt_pos : 0 < Real.sqrt (b r) := Real.sqrt_pos.mpr hb
  have hsqrt_ne : Real.sqrt (b r) ≠ 0 := hsqrt_pos.ne'
  have hquad : b r * θ ^ 2 / 2 = x ^ 2 / 2 := by
    dsimp [θ]
    rw [div_pow]
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt hb.le]
    ring
  have hphaseR : (n : ℝ) * θ = a r * θ := by
    rw [ha]
  have hphaseC :
      Complex.exp (-(↑↑n * ↑θ) * I) =
        Complex.exp (-(a r * θ : ℝ) * I) := by
    congr 1
    have hmulC : (n : ℂ) * (θ : ℂ) = ((a r * θ : ℝ) : ℂ) := by
      exact_mod_cast hphaseR
    rw [hmulC]
  have hden :
      Complex.exp (-(b r * θ ^ 2 / 2 : ℝ)) =
        Complex.exp ((-(x ^ 2) / 2 : ℝ) : ℂ) := by
    congr 1
    exact_mod_cast (by linarith [hquad] :
      -(b r * θ ^ 2 / 2) = -(x ^ 2) / 2)
  have hgauss :
      Complex.exp (-(x ^ 2) / 2) =
        Complex.exp ((-(x ^ 2) / 2 : ℝ) : ℂ) := by
    congr 1
    norm_num
  dsimp [θ] at hphaseC hden ⊢
  rw [hgauss]
  unfold saddleGAt saddleLocalRatio
  rw [hphaseC, hden]
  field_simp [Complex.exp_ne_zero ((-(x ^ 2) / 2 : ℝ) : ℂ)]

lemma saddleGAt_continuous_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    Continuous fun θ : ℝ => saddleGAt f r n θ := by
  have hfcirc0 : Continuous fun θ : ℝ => f (circleMap (0 : ℂ) r θ) :=
    hf.continuousOn.comp_continuous (continuous_circleMap (0 : ℂ) r)
      (fun θ => circleMap_mem_closedBall (0 : ℂ) hr θ)
  have hfcirc :
      Continuous fun θ : ℝ =>
        f ((r : ℂ) * Complex.exp (θ * Complex.I)) := by
    simpa [circleMap_zero] using hfcirc0
  have hphase :
      Continuous fun θ : ℝ => Complex.exp (-(↑↑n * ↑θ) * I) := by
    fun_prop
  simpa [saddleGAt, div_eq_mul_inv] using
    (hfcirc.mul continuous_const).mul hphase

lemma saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (a b : ℝ) (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    IntervalIntegrable (saddleGAt f r n) volume a b :=
  (saddleGAt_continuous_of_differentiableOn_closedBall f r n hr hf).intervalIntegrable a b

lemma saddleJtAt_norm_le_of_tail_bound
    (f : ℂ → ℂ) (r δ E : ℝ) (n : ℕ)
    (hδ_nonneg : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (hE_nonneg : 0 ≤ E)
    (htail : ∀ θ : ℝ, δ ≤ |θ| → |θ| ≤ Real.pi →
      ‖saddleGAt f r n θ‖ ≤ E) :
    ‖saddleJtAt f r δ n‖ ≤
      (‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)) * E := by
  have hleft :
      ‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ ≤
        E * |(-δ) - (-Real.pi)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    have hθI : -Real.pi < θ ∧ θ ≤ -δ := by
      simpa [Set.uIoc_of_le (by linarith : -Real.pi ≤ -δ)] using hθ
    have hθ_nonpos : θ ≤ 0 := by linarith
    have hδθ : δ ≤ |θ| := by
      rw [abs_of_nonpos hθ_nonpos]
      linarith
    have hθπ : |θ| ≤ Real.pi := by
      rw [abs_of_nonpos hθ_nonpos]
      linarith
    exact htail θ hδθ hθπ
  have hright :
      ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖ ≤
        E * |Real.pi - δ| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    have hθI : δ < θ ∧ θ ≤ Real.pi := by
      simpa [Set.uIoc_of_le hδπ] using hθ
    have hθ_nonneg : 0 ≤ θ := by linarith
    have hδθ : δ ≤ |θ| := by
      rw [abs_of_nonneg hθ_nonneg]
      linarith
    have hθπ : |θ| ≤ Real.pi := by
      rw [abs_of_nonneg hθ_nonneg]
      exact hθI.2
    exact htail θ hδθ hθπ
  have hlen_right : |Real.pi - δ| ≤ Real.pi := by
    rw [abs_of_nonneg (sub_nonneg.mpr hδπ)]
    linarith [Real.pi_pos]
  have hlen_left : |(-δ) - (-Real.pi)| ≤ Real.pi := by
    rw [show (-δ) - (-Real.pi) = Real.pi - δ by ring]
    exact hlen_right
  have hleft_pi :
      ‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ ≤
        E * Real.pi :=
    hleft.trans (mul_le_mul_of_nonneg_left hlen_left hE_nonneg)
  have hright_pi :
      ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖ ≤
        E * Real.pi :=
    hright.trans (mul_le_mul_of_nonneg_left hlen_right hE_nonneg)
  unfold saddleJtAt
  calc
    ‖(2 * Real.pi : ℂ)⁻¹ *
        ((∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ) +
          ∫ θ in δ..Real.pi, saddleGAt f r n θ)‖
        ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ *
          (‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ +
            ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ * (E * Real.pi + E * Real.pi) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hleft_pi hright_pi) (norm_nonneg _)
    _ = (‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)) * E := by
          ring

lemma f_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro hzero
  simp [hzero] at hz

lemma saddleScale_nonzero_of_pos
    (f : ℂ → ℂ) (r B : ℕ → ℝ) (n : ℕ)
    (hr : 0 < r n) (hf : 0 < (f (r n : ℂ)).re) (hB : 0 < B n) :
    saddleScale f r B n ≠ 0 := by
  have hfnz : f (r n : ℂ) ≠ 0 := f_ne_zero_of_re_pos hf
  have hrC : (r n : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hpow : (r n : ℂ) ^ n ≠ 0 := pow_ne_zero n hrC
  have hpref : saddlePref f r n ≠ 0 := by
    unfold saddlePref saddlePrefAt
    exact div_ne_zero hfnz hpow
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * B n) := by
    exact Real.sqrt_pos.mpr (by positivity)
  have hsqrtC : (Real.sqrt (2 * Real.pi * B n) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_pos.ne'
  unfold saddleScale
  exact div_ne_zero hpref hsqrtC

end
end

section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Gaussian moments for the saddle correction

This file records the standard Gaussian moments needed by the second-order
saddle correction.
-/

open Complex Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

private lemma deriv_gaussianMGFCore :
    deriv gaussianMGFCore = fun t : ℝ => t * gaussianMGFCore t := by
  ext t
  unfold gaussianMGFCore
  rw [_root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
    Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring

private lemma deriv_t_mul_gaussianMGFCore :
    deriv (fun t : ℝ => t * gaussianMGFCore t) =
      fun t : ℝ => (1 + t ^ 2) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp
  ring_nf

private lemma deriv_poly2_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (1 + t ^ 2) * gaussianMGFCore t) =
      fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.add, deriv_fun_add, deriv_const',
    deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring_nf

private lemma deriv_poly3_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCore t) =
      fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly : deriv (fun t : ℝ => 3 * t + t ^ 3) t = 3 + 3 * t ^ 2 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 3 * y) t = 3 := by
      rw [deriv_const_mul_field (u := (3 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hpow : deriv (fun y : ℝ => y ^ 3) t = 3 * t ^ 2 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hpow]
  rw [hpoly]
  ring_nf

private lemma deriv_poly4_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCore t) =
      fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const', deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one,
    pow_one, deriv_id'', mul_one, zero_add]
  have hpoly :
      deriv (fun t : ℝ => 3 + 6 * t ^ 2 + t ^ 4) t =
        12 * t + 4 * t ^ 3 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hconst : deriv (fun _ : ℝ => (3 : ℝ)) t = 0 := by
      rw [deriv_const']
    have hquad : deriv (fun y : ℝ => 6 * y ^ 2) t = 12 * t := by
      rw [deriv_const_mul_field (u := (6 : ℝ)) (v := fun y : ℝ => y ^ 2) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquart : deriv (fun y : ℝ => y ^ 4) t = 4 * t ^ 3 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hconst, hquad, hquart]
  rw [hpoly]
  ring_nf

private lemma deriv_poly5_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCore t) =
      fun t : ℝ => (15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly :
      deriv (fun t : ℝ => 15 * t + 10 * t ^ 3 + t ^ 5) t =
        15 + 30 * t ^ 2 + 5 * t ^ 4 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 15 * y) t = 15 := by
      rw [deriv_const_mul_field (u := (15 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 10 * y ^ 3) t = 30 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (10 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => y ^ 5) t = 5 * t ^ 4 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint]
  rw [hpoly]
  ring_nf

lemma gaussianReal_moment_four :
    (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)) = (3 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1))
        = iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 3 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 4 gaussianMGFCore 0 = 3
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCore, deriv_t_mul_gaussianMGFCore,
        deriv_poly2_mul_gaussianMGFCore, deriv_poly3_mul_gaussianMGFCore]
      simp [gaussianMGFCore]

lemma gaussianReal_moment_six :
    (∫ x : ℝ, x ^ 6 ∂(gaussianReal 0 1)) = (15 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 6 ∂(gaussianReal 0 1))
        = iteratedDeriv 6 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 15 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 6 gaussianMGFCore 0 = 15
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCore, deriv_t_mul_gaussianMGFCore,
        deriv_poly2_mul_gaussianMGFCore, deriv_poly3_mul_gaussianMGFCore,
        deriv_poly4_mul_gaussianMGFCore, deriv_poly5_mul_gaussianMGFCore]
      simp [gaussianMGFCore]

lemma gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [gaussianPDFReal]

private lemma gaussian_weighted_moment_from_probability (k : ℕ) (m : ℝ)
    (hm : (∫ x : ℝ, x ^ k ∂(gaussianReal 0 1)) = m) :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) =
      Real.sqrt (2 * Real.pi) * m := by
  have hprob :=
    integral_gaussianReal_eq_integral_smul
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      (f := fun x : ℝ => x ^ k) (by norm_num : (1 : ℝ≥0) ≠ 0)
  rw [hm] at hprob
  rw [show (∫ x : ℝ, gaussianPDFReal 0 1 x • x ^ k) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k by
        simp_rw [gaussianPDFReal_zero_one, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        refine ae_of_all _ ?_
        intro x
        ring] at hprob
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hsqrt_pos.ne'
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k)
        = Real.sqrt (2 * Real.pi) *
            ((Real.sqrt (2 * Real.pi))⁻¹ *
              ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) := by
          field_simp [hsqrt_ne]
    _ = Real.sqrt (2 * Real.pi) * m := by rw [← hprob]

lemma gaussian_weighted_moment_four :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 4) =
      3 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 4)
        = Real.sqrt (2 * Real.pi) * 3 :=
          gaussian_weighted_moment_from_probability 4 3 gaussianReal_moment_four
    _ = 3 * Real.sqrt (2 * Real.pi) := by ring

lemma gaussian_weighted_moment_six :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 6) =
      15 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 6)
        = Real.sqrt (2 * Real.pi) * 15 :=
          gaussian_weighted_moment_from_probability 6 15 gaussianReal_moment_six
    _ = 15 * Real.sqrt (2 * Real.pi) := by ring

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

/-- The formal series used by the H-admissible interface. -/
noncomputable abbrev involSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS involCarrier

/-- The quadratic inner PowerSeries `z + z^2/2`. -/
def involInnerPS : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) + (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2

lemma involInnerPS_constantCoeff : PowerSeries.constantCoeff involInnerPS = 0 := by
  unfold involInnerPS
  have hX : PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ) = 0 :=
    _root_.PowerSeries.constantCoeff_X
  have hpow : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) =
      (PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ)) ^ 2 :=
    _root_.map_pow (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) 2
  have hpow0 : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) = 0 :=
    hpow.trans ((congrArg (fun z : ℂ => z ^ 2) hX).trans (by norm_num))
  have hsmul : PowerSeries.constantCoeff (R := ℂ)
      ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) =
        (2⁻¹ : ℂ) • PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) :=
    _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℂ) ^ 2) (2⁻¹ : ℂ)
  have hsmul0 : PowerSeries.constantCoeff (R := ℂ)
      ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) = 0 :=
    hsmul.trans ((congrArg (fun z : ℂ => (2⁻¹ : ℂ) • z) hpow0).trans (smul_zero _))
  have hadd : PowerSeries.constantCoeff (R := ℂ)
      ((PowerSeries.X : PowerSeries ℂ) + (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) =
        PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ) +
          PowerSeries.constantCoeff (R := ℂ) ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) :=
    _root_.map_add (PowerSeries.constantCoeff (R := ℂ))
      (PowerSeries.X : PowerSeries ℂ) ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)
  exact hadd.trans
    ((congrArg₂ (fun x y : ℂ => x + y) hX hsmul0).trans (add_zero (0 : ℂ)))

theorem involCarrier_eq_complex_subst :
    involCarrier = (PowerSeries.exp ℂ).subst involInnerPS := by
  rw [involCarrier, AnalyticCombinatorics.Ch1.CombClass.egf_involutions]
  have hsubst : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℚ) + (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    have hX : PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ) = 0 :=
      _root_.PowerSeries.constantCoeff_X
    have hpow : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) =
        (PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ)) ^ 2 :=
      _root_.map_pow (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) 2
    have hpow0 : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) = 0 :=
      hpow.trans ((congrArg (fun z : ℚ => z ^ 2) hX).trans (by norm_num))
    have hsmul : PowerSeries.constantCoeff (R := ℚ)
        ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) =
          (2⁻¹ : ℚ) • PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) :=
      _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℚ) ^ 2) (2⁻¹ : ℚ)
    have hsmul0 : PowerSeries.constantCoeff (R := ℚ)
        ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) = 0 :=
      hsmul.trans ((congrArg (fun z : ℚ => (2⁻¹ : ℚ) • z) hpow0).trans (smul_zero _))
    have hadd : PowerSeries.constantCoeff (R := ℚ)
        ((PowerSeries.X : PowerSeries ℚ) + (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) =
          PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ) +
            PowerSeries.constantCoeff (R := ℚ) ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) :=
      _root_.map_add (PowerSeries.constantCoeff (R := ℚ))
        (PowerSeries.X : PowerSeries ℚ) ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)
    exact hadd.trans
      ((congrArg₂ (fun x y : ℚ => x + y) hX hsmul0).trans (add_zero (0 : ℚ)))
  have hmap_inner :
      (((PowerSeries.X : PowerSeries ℚ) +
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2).map (algebraMap ℚ ℂ)) =
        involInnerPS := by
    ext n
    by_cases hn : n = 2
    · subst n
      norm_num [involInnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
    · simp [involInnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow, hn]
  have hmap_exp :
      (PowerSeries.exp ℚ).map (algebraMap ℚ ℂ) = PowerSeries.exp ℂ := by
    ext n
    simp
  change (((PowerSeries.exp ℚ).subst
        ((PowerSeries.X : PowerSeries ℚ) + (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)).map
      (algebraMap ℚ ℂ)) = _
  rw [PowerSeries.map_subst
    (a := ((PowerSeries.X : PowerSeries ℚ) +
      (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2))
    (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ)]
  rw [hmap_exp]
  change (PowerSeries.exp ℂ).subst
      ((((PowerSeries.X : PowerSeries ℚ) +
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2).map (algebraMap ℚ ℂ))) =
    (PowerSeries.exp ℂ).subst involInnerPS
  rw [hmap_inner]

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

lemma involInner_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => z + z ^ 2 / 2)
      (PowerSeries.toFMLS involInnerPS) (0 : ℂ) := by
  have hX : HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) :=
    hasFPowerSeriesAt_id_toFMLS_X
  have hX2 : HasFPowerSeriesAt (fun z : ℂ => z * z)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using hasFPowerSeriesAt_mul_toFMLS hX hX
  have hhalf : HasFPowerSeriesAt (fun z : ℂ => (2⁻¹ : ℂ) • (z * z))
      ((2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
    simpa using (HasFPowerSeriesAt.const_smul (c := (2⁻¹ : ℂ)) hX2)
  have hsum := hX.add hhalf
  have hseries :
      PowerSeries.toFMLS involInnerPS =
        PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ) +
          (2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2) := by
    ext n
    simp [involInnerPS, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]
  rw [hseries]
  convert hsum using 1
  funext z
  simp [smul_eq_mul]
  ring_nf

lemma involFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt involFun involSeries (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS (PowerSeries.exp ℂ))
      ((fun z : ℂ => z + z ^ 2 / 2) 0) := by
    simpa using ExpStirling.expCarrier_hasFPowerSeriesAt_zero
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => z + z ^ 2 / 2) houter involInner_hasFPowerSeriesAt_zero
  change HasFPowerSeriesAt involFun (PowerSeries.toFMLS involCarrier) (0 : ℂ)
  rw [involCarrier_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp involInnerPS_constantCoeff]
  simpa [Function.comp_def, involFun, involSeries] using hcomp

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

/-- The exact exponent left after removing the linear and quadratic saddle terms. -/
def involLocalExponent (r θ : ℝ) : ℂ :=
  (r : ℂ) * ExpStirling.expLocalRemainder θ +
    (((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))

lemma complex_two_mul_theta_I (θ : ℝ) :
    (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
      ((2 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma invol_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio involFun involSaddleAReal involSaddleBReal r θ =
      Complex.exp (involLocalExponent r θ) := by
  unfold saddleLocalRatio involFun involLocalExponent involSaddleAReal involSaddleBReal
  have hsq_full :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
        ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
    rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
        ((2 * θ : ℝ) : ℂ) * Complex.I by
      simpa using complex_two_mul_theta_I θ]
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  rw [ExpStirling.expLocalRemainder_eq θ]
  rw [ExpStirling.expLocalRemainder_eq (2 * θ)]
  rw [hsq_full]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow]
  ring_nf

lemma invol_f_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < (involFun (r : ℂ)).re := by
  refine Eventually.of_forall fun r => ?_
  unfold involFun
  have harg : (r : ℂ) + (r : ℂ) ^ 2 / 2 = ((r + r ^ 2 / 2 : ℝ) : ℂ) := by
    norm_num
  have hval :
      Complex.exp (((r + r ^ 2 / 2 : ℝ) : ℂ)) =
        ((Real.exp (r + r ^ 2 / 2) : ℝ) : ℂ) := by
    simp
  rw [harg, hval]
  exact Real.exp_pos (r + r ^ 2 / 2)

lemma invol_b_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < involSaddleBReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold involSaddleBReal
  positivity

lemma invol_delta_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < involSaddleDeltaReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold involSaddleDeltaReal
  exact Real.rpow_pos_of_pos hr _

lemma invol_delta_tendsto_zero :
    Tendsto involSaddleDeltaReal atTop (𝓝 0) := by
  simpa [involSaddleDeltaReal] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4))

lemma invol_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in atTop, involSaddleDeltaReal r ≤ Real.pi :=
  invol_delta_tendsto_zero.eventually_le_const Real.pi_pos

lemma invol_delta_le_one_eventually :
    ∀ᶠ r : ℝ in atTop, involSaddleDeltaReal r ≤ 1 :=
  invol_delta_tendsto_zero.eventually_le_const zero_lt_one

lemma invol_delta_mul_r_eq_rpow_eventually :
    (fun r : ℝ => involSaddleDeltaReal r * r) =ᶠ[atTop]
      fun r : ℝ => r ^ (1 / 4 : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  calc
    involSaddleDeltaReal r * r
        = r ^ (-(3 / 4 : ℝ)) * r ^ (1 : ℝ) := by
          simp [involSaddleDeltaReal, Real.rpow_one]
    _ = r ^ (-(3 / 4 : ℝ) + (1 : ℝ)) := by
          rw [Real.rpow_add hr]
    _ = r ^ (1 / 4 : ℝ) := by norm_num

lemma invol_delta_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))
      atTop atTop := by
  have hpow : Tendsto (fun r : ℝ => r ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [eventually_ge_atTop (1 : ℝ), invol_delta_mul_r_eq_rpow_eventually] with
    r hr heq
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := by
    unfold involSaddleBReal
    nlinarith [sq_nonneg r]
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := by
    exact Real.le_sqrt_of_sq_le hb_ge
  have hδ_nonneg : 0 ≤ involSaddleDeltaReal r := by
    unfold involSaddleDeltaReal
    positivity
  calc
    r ^ (1 / 4 : ℝ) = involSaddleDeltaReal r * r := heq.symm
    _ ≤ involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r) :=
      mul_le_mul_of_nonneg_left hsqrt_ge hδ_nonneg

lemma invol_differentiableOn_eventually :
    ∀ᶠ r : ℝ in atTop,
      DifferentiableOn ℂ involFun (Metric.closedBall (0 : ℂ) r) := by
  refine Eventually.of_forall fun r => ?_
  unfold involFun
  fun_prop

def involLocalControl (r : ℝ) : ℝ :=
  r ^ 2 * (involSaddleDeltaReal r) ^ 3

lemma involLocalControl_eq_rpow_eventually :
    involLocalControl =ᶠ[atTop] fun r : ℝ => r ^ (-(1 / 4 : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hr0 : 0 ≤ r := hr.le
  have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
    exact (Real.rpow_natCast r 2).symm
  have hdelta_pow :
      (r ^ (-(3 / 4 : ℝ))) ^ 3 = r ^ (-(3 / 4 : ℝ) * (3 : ℝ)) :=
    (Real.rpow_mul_natCast hr0 (-(3 / 4 : ℝ)) 3).symm
  unfold involLocalControl involSaddleDeltaReal
  calc
    r ^ 2 * (r ^ (-(3 / 4 : ℝ))) ^ 3
        = r ^ (2 : ℝ) * r ^ (-(3 / 4 : ℝ) * (3 : ℝ)) := by
          rw [hr2_rpow, hdelta_pow]
    _ = r ^ ((2 : ℝ) + (-(3 / 4 : ℝ) * (3 : ℝ))) := by
          rw [Real.rpow_add hr]
    _ = r ^ (-(1 / 4 : ℝ)) := by norm_num

lemma involLocalControl_tendsto_zero :
    Tendsto involLocalControl atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => r ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  exact Tendsto.congr' involLocalControl_eq_rpow_eventually.symm hpow

def involLocalConstant : ℝ :=
  40 * Real.exp 2

lemma involLocalBound_tendsto_zero :
    Tendsto (fun r : ℝ => involLocalConstant * involLocalControl r) atTop (𝓝 0) := by
  simpa using involLocalControl_tendsto_zero.const_mul involLocalConstant

lemma expLocalRemainder_norm_le_exp_two {θ : ℝ} (hθ : |θ| ≤ 2) :
    ‖ExpStirling.expLocalRemainder θ‖ ≤ Real.exp 2 * |θ| ^ 3 := by
  calc
    ‖ExpStirling.expLocalRemainder θ‖ ≤ |θ| ^ 3 * Real.exp |θ| :=
      ExpStirling.expLocalRemainder_norm_le θ
    _ ≤ |θ| ^ 3 * Real.exp 2 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 3)
    _ = Real.exp 2 * |θ| ^ 3 := by ring

lemma invol_local_exponent_norm_le_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ θ : ℝ, |θ| ≤ involSaddleDeltaReal r →
      ‖involLocalExponent r θ‖ ≤ involLocalConstant * involLocalControl r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), invol_delta_le_one_eventually] with
    r hr hδ_le_one θ hθδ
  let δ : ℝ := involSaddleDeltaReal r
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, involSaddleDeltaReal]
    positivity
  have hθ_one : |θ| ≤ 1 := hθδ.trans hδ_le_one
  have hθ_two : |θ| ≤ 2 := hθ_one.trans (by norm_num)
  have h2θ_two : |2 * θ| ≤ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hθ_one]
  have hθ3δ3 : |θ| ^ 3 ≤ δ ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg θ) hθδ 3
  have h2θ3 : |2 * θ| ^ 3 ≤ 8 * δ ^ 3 := by
    calc
      |2 * θ| ^ 3 = 8 * |θ| ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      _ ≤ 8 * δ ^ 3 := mul_le_mul_of_nonneg_left hθ3δ3 (by norm_num)
  have hrem1 := expLocalRemainder_norm_le_exp_two hθ_two
  have hrem2 := expLocalRemainder_norm_le_exp_two h2θ_two
  have hterm1 :
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ ≤
        Real.exp 2 * (r * δ ^ 3) := by
    calc
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖
          = r * ‖ExpStirling.expLocalRemainder θ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (Real.exp 2 * |θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem1 hr0
      _ ≤ r * (Real.exp 2 * δ ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθ3δ3 (Real.exp_pos 2).le) hr0
      _ = Real.exp 2 * (r * δ ^ 3) := by ring_nf
  have hterm2 :
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ ≤
        4 * Real.exp 2 * (r ^ 2 * δ ^ 3) := by
    have hcoef0 : 0 ≤ r ^ 2 / 2 := by positivity
    calc
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖
          = (r ^ 2 / 2) * ‖ExpStirling.expLocalRemainder (2 * θ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
      _ ≤ (r ^ 2 / 2) * (Real.exp 2 * |2 * θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem2 hcoef0
      _ ≤ (r ^ 2 / 2) * (Real.exp 2 * (8 * δ ^ 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2θ3 (Real.exp_pos 2).le) hcoef0
      _ = 4 * Real.exp 2 * (r ^ 2 * δ ^ 3) := by ring
  have hterm1' :
      Real.exp 2 * (r * δ ^ 3) ≤ Real.exp 2 * (r ^ 2 * δ ^ 3) := by
    have hr_le_r2 : r ≤ r ^ 2 := by nlinarith [hr]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr_le_r2 (pow_nonneg hδ0 3)) (Real.exp_pos 2).le
  calc
    ‖involLocalExponent r θ‖
        ≤ ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ +
          ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ :=
        norm_add_le _ _
    _ ≤ Real.exp 2 * (r * δ ^ 3) + 4 * Real.exp 2 * (r ^ 2 * δ ^ 3) :=
        add_le_add hterm1 hterm2
    _ ≤ Real.exp 2 * (r ^ 2 * δ ^ 3) + 4 * Real.exp 2 * (r ^ 2 * δ ^ 3) :=
        add_le_add hterm1' (le_refl _)
    _ = 5 * Real.exp 2 * (r ^ 2 * δ ^ 3) := by ring_nf
    _ ≤ involLocalConstant * involLocalControl r := by
      unfold involLocalConstant involLocalControl
      dsimp [δ]
      have hnonneg : 0 ≤ r ^ 2 * (r ^ (-(3 / 4 : ℝ))) ^ 3 := by
        positivity
      nlinarith [Real.exp_pos 2, hnonneg]

lemma invol_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in atTop, ∀ θ : ℝ,
      |θ| ≤ involSaddleDeltaReal r →
        ‖saddleLocalRatio involFun involSaddleAReal involSaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in atTop, involLocalConstant * involLocalControl r ≤ ε / 2 :=
    involLocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in atTop, involLocalConstant * involLocalControl r ≤ 1 :=
    involLocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [invol_local_exponent_norm_le_eventually, hsmall, hone] with
    r hloc hsmallr honer θ hθ
  rw [invol_saddleLocalRatio_eq]
  have hz : ‖involLocalExponent r θ‖ ≤ involLocalConstant * involLocalControl r :=
    hloc θ hθ
  have hz_one : ‖involLocalExponent r θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp (involLocalExponent r θ) - 1‖
        ≤ 2 * ‖involLocalExponent r θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 * (involLocalConstant * involLocalControl r) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

lemma invol_saddleGAt_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt involFun r n θ‖ =
      Real.exp (r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)) := by
  unfold saddleGAt involFun
  have hphase : ‖Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hden :
      ‖Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2)‖ =
        Real.exp (r + r ^ 2 / 2) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.add_re]
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
    rw [hsq]
    simp
  have hnum_re :
      (((r : ℂ) * Complex.exp (θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 / 2).re =
        r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) := by
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
    rw [hsq_div]
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
    rw [Complex.add_re, hre1, hre2]
  have hnum :
      ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2)‖ =
        Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ)) := by
    rw [Complex.norm_exp, hnum_re]
  have hden_pos : 0 < Real.exp (r + r ^ 2 / 2) := Real.exp_pos _
  calc
    ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2) /
        Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2) *
        Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖
        = Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ)) /
            Real.exp (r + r ^ 2 / 2) := by
          rw [norm_mul, hphase, mul_one, norm_div, hnum, hden]
    _ = Real.exp (r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)) := by
      rw [← Real.exp_sub]
      congr 1
      ring_nf

def involTailE (r : ℝ) : ℝ :=
  Real.exp (-(1 / (2 * Real.pi ^ 2)) * r ^ (1 / 4 : ℝ))

lemma involTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ involTailE r :=
  Eventually.of_forall fun r => by
    unfold involTailE
    positivity

lemma involTailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r)
      atTop (𝓝 0) := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (4 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℝ) c hc
  have hy : Tendsto (fun r : ℝ => r ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hcomp :
      Tendsto (fun r : ℝ => (r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
        Real.exp (-c * r ^ (1 / 4 : ℝ))) atTop (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto (fun r : ℝ => Real.sqrt (6 * Real.pi) *
        ((r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
          Real.exp (-c * r ^ (1 / 4 : ℝ)))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (6 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · exact Eventually.of_forall fun r => by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hB_le : involSaddleBReal r ≤ 3 * r ^ 2 := by
      unfold involSaddleBReal
      nlinarith [hr]
    have hsqrt :
        Real.sqrt (2 * Real.pi * involSaddleBReal r) ≤
          Real.sqrt (6 * Real.pi) * r := by
      have hmul : 2 * Real.pi * involSaddleBReal r ≤ 6 * Real.pi * r ^ 2 := by
        calc
          2 * Real.pi * involSaddleBReal r
              ≤ 2 * Real.pi * (3 * r ^ 2) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 6 * Real.pi * r ^ 2 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * involSaddleBReal r)
            ≤ Real.sqrt (6 * Real.pi * r ^ 2) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (6 * Real.pi) * r := by
          have h6pi : 0 ≤ 6 * Real.pi := by positivity
          rw [Real.sqrt_mul h6pi (r ^ 2)]
          rw [Real.sqrt_sq hr0]
    have hrpow4 : (r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = r := by
      rw [← Real.rpow_mul hr0,
        show (1 / 4 : ℝ) * 4 = 1 by norm_num, Real.rpow_one]
    calc
      Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r
          ≤ (Real.sqrt (6 * Real.pi) * r) * involTailE r :=
            mul_le_mul_of_nonneg_right hsqrt (by
              unfold involTailE
              positivity)
      _ = Real.sqrt (6 * Real.pi) *
            ((r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
              Real.exp (-c * r ^ (1 / 4 : ℝ))) := by
        unfold involTailE
        dsimp [c]
        rw [hrpow4]
        ring_nf

lemma invol_tail_bound_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
      involSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt involFun r n θ‖ ≤ involTailE r := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hc_le_one : c ≤ 1 := by
    dsimp [c]
    have hden : 1 ≤ 2 * Real.pi ^ 2 := by
      nlinarith [Real.two_le_pi]
    have hden_pos : 0 < 2 * Real.pi ^ 2 := by positivity
    rw [div_le_iff₀ hden_pos]
    nlinarith
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr n θ hδθ hθπ
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ involSaddleDeltaReal r := by
    unfold involSaddleDeltaReal
    positivity
  rw [invol_saddleGAt_norm]
  unfold involTailE
  apply Real.exp_le_exp.mpr
  have htarget_quarter : c * r ^ (1 / 4 : ℝ) ≤ r := by
    have hpow_le : r ^ (1 / 4 : ℝ) ≤ r := by
      calc
        r ^ (1 / 4 : ℝ) ≤ r ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1 / 4 : ℝ) ≤ 1)
        _ = r := by rw [Real.rpow_one]
    calc
      c * r ^ (1 / 4 : ℝ) ≤ 1 * r ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hc_le_one (Real.rpow_nonneg hr0 _)
      _ ≤ r := by simpa using hpow_le
  by_cases hsmall : |θ| ≤ Real.pi / 2
  · have h2θπ : |2 * θ| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hcos2 := Real.cos_le_one_sub_mul_cos_sq h2θπ
    have hcos2_sub : Real.cos (2 * θ) - 1 ≤
        -(2 / Real.pi ^ 2) * (2 * θ) ^ 2 := by
      linarith
    have hquad :
        r ^ 2 * (involSaddleDeltaReal r) ^ 2 = r ^ (1 / 2 : ℝ) := by
      have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
        exact (Real.rpow_natCast r 2).symm
      have hdelta_pow :
          (r ^ (-(3 / 4 : ℝ))) ^ 2 = r ^ (-(3 / 4 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hr0 (-(3 / 4 : ℝ)) 2).symm
      unfold involSaddleDeltaReal
      calc
        r ^ 2 * (r ^ (-(3 / 4 : ℝ))) ^ 2
            = r ^ (2 : ℝ) * r ^ (-(3 / 4 : ℝ) * (2 : ℝ)) := by
              rw [hr2_rpow, hdelta_pow]
        _ = r ^ ((2 : ℝ) + (-(3 / 4 : ℝ) * (2 : ℝ))) := by
              rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hr)]
        _ = r ^ (1 / 2 : ℝ) := by norm_num
    have hθsq : (involSaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
      calc
        (involSaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ hδ0 hδθ 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hmain :
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
          ≤ -c * r ^ (1 / 4 : ℝ) := by
      have hcos1_nonpos : Real.cos θ - 1 ≤ 0 := by
        linarith [Real.cos_le_one θ]
      have hleft_nonpos : r * (Real.cos θ - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hr0 hcos1_nonpos
      have hcoef_nonpos : -(4 / Real.pi ^ 2) ≤ 0 := by
        have hpos : 0 ≤ 4 / Real.pi ^ 2 := by positivity
        linarith
      have hquad_lower : r ^ (1 / 4 : ℝ) ≤ r ^ (1 / 2 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
      have hstrong :
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
            ≤ -(4 / Real.pi ^ 2) * (r ^ 2 * (involSaddleDeltaReal r) ^ 2) := by
        calc
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
              ≤ (r ^ 2 / 2) * (-(2 / Real.pi ^ 2) * (2 * θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hcos2_sub (by positivity)
          _ = -(4 / Real.pi ^ 2) * (r ^ 2 * θ ^ 2) := by ring_nf
          _ ≤ -(4 / Real.pi ^ 2) * (r ^ 2 * (involSaddleDeltaReal r) ^ 2) := by
            exact mul_le_mul_of_nonpos_left
              (mul_le_mul_of_nonneg_left hθsq (sq_nonneg r)) hcoef_nonpos
      have hconst : c * r ^ (1 / 4 : ℝ) ≤
          (4 / Real.pi ^ 2) * (r ^ 2 * (involSaddleDeltaReal r) ^ 2) := by
        rw [hquad]
        have hc4 : c ≤ 4 / Real.pi ^ 2 := by
          dsimp [c]
          field_simp [Real.pi_ne_zero]
          norm_num
        calc
          c * r ^ (1 / 4 : ℝ) ≤ c * r ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hquad_lower hcpos.le
          _ ≤ (4 / Real.pi ^ 2) * r ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hc4 (Real.rpow_nonneg hr0 _)
      calc
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
            ≤ 0 + (-(4 / Real.pi ^ 2) *
                (r ^ 2 * (involSaddleDeltaReal r) ^ 2)) :=
              add_le_add hleft_nonpos hstrong
        _ ≤ -c * r ^ (1 / 4 : ℝ) := by linarith
    exact hmain
  · have hlarge : Real.pi / 2 < |θ| := lt_of_not_ge hsmall
    have hcos_nonpos : Real.cos θ ≤ 0 := by
      by_cases hθnonneg : 0 ≤ θ
      · have hθ_le_pi : θ ≤ Real.pi := (abs_le.mp hθπ).2
        have hpi2_le : Real.pi / 2 ≤ θ := by
          have habs_eq : |θ| = θ := abs_of_nonneg hθnonneg
          linarith
        exact Real.cos_nonpos_of_pi_div_two_le_of_le hpi2_le (by linarith [hθ_le_pi])
      · have hθneg : θ < 0 := lt_of_not_ge hθnonneg
        have hneg_le_pi : -θ ≤ Real.pi := by
          have h := (abs_le.mp hθπ).1
          linarith
        have hpi2_le_neg : Real.pi / 2 ≤ -θ := by
          have habs_eq : |θ| = -θ := abs_of_neg hθneg
          linarith
        have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le hpi2_le_neg
          (by linarith [hneg_le_pi])
        simpa [Real.cos_neg] using hcos
    have hcos2_nonpos : Real.cos (2 * θ) - 1 ≤ 0 := by
      linarith [Real.cos_le_one (2 * θ)]
    have hmain :
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
          ≤ -c * r ^ (1 / 4 : ℝ) := by
      have hfirst : r * (Real.cos θ - 1) ≤ -r := by
        have hcos_sub : Real.cos θ - 1 ≤ -1 := by linarith
        calc
          r * (Real.cos θ - 1) ≤ r * (-1) :=
            mul_le_mul_of_nonneg_left hcos_sub hr0
          _ = -r := by ring
      have hsecond : (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos2_nonpos
      calc
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
            ≤ -r + 0 := add_le_add hfirst hsecond
        _ ≤ -c * r ^ (1 / 4 : ℝ) := by linarith
    exact hmain

lemma invol_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in atTop, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * involSaddleBReal r) * E r)
        atTop (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        involSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt involFun r n θ‖ ≤ E r) := by
  exact ⟨involTailE, involTailE_nonneg_eventually, involTailE_decay, invol_tail_bound_eventually⟩

lemma involSaddleRadius_nonneg (n : ℕ) : 0 ≤ involSaddleRadius n := by
  unfold involSaddleRadius
  have hle : 1 ≤ Real.sqrt (1 + 4 * (n : ℝ)) := by
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hle' : Real.sqrt (1 : ℝ) ≤ Real.sqrt (1 + 4 * (n : ℝ)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    simpa only [Real.sqrt_one] using hle'
  linarith

lemma involSaddleAReal_radius (n : ℕ) :
    involSaddleAReal (involSaddleRadius n) = (n : ℝ) := by
  unfold involSaddleAReal involSaddleRadius
  have hnonneg : 0 ≤ 1 + 4 * (n : ℝ) := by positivity
  have hs : Real.sqrt (1 + 4 * (n : ℝ)) ^ 2 = 1 + 4 * (n : ℝ) :=
    Real.sq_sqrt hnonneg
  nlinarith

lemma involSaddleAReal_strictMonoOn_nonneg :
    StrictMonoOn involSaddleAReal (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold involSaddleAReal
  have hpos : 0 < (y - x) * (1 + x + y) := by
    have hdiff : 0 < y - x := sub_pos.mpr hxy
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have hsum : 0 < 1 + x + y := by linarith
    exact mul_pos hdiff hsum
  nlinarith

lemma involSaddleRadius_tendsto_atTop :
    Tendsto involSaddleRadius atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  let M0 : ℝ := max M 0
  obtain ⟨N, hN⟩ := exists_nat_gt (involSaddleAReal M0)
  refine ⟨N, fun n hn => ?_⟩
  have hM0_nonneg : 0 ≤ M0 := le_max_right _ _
  have hM_le_M0 : M ≤ M0 := le_max_left _ _
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAM0_lt_n : involSaddleAReal M0 < (n : ℝ) := hN.trans_le hnR
  by_contra hnot
  have hr_lt_M : involSaddleRadius n < M := lt_of_not_ge hnot
  have hr_lt_M0 : involSaddleRadius n < M0 := hr_lt_M.trans_le hM_le_M0
  have hstrict :
      involSaddleAReal (involSaddleRadius n) < involSaddleAReal M0 :=
    involSaddleAReal_strictMonoOn_nonneg
      (involSaddleRadius_nonneg n) hM0_nonneg hr_lt_M0
  rw [involSaddleAReal_radius] at hstrict
  linarith

def involHAdmissible : HAdmissible involFun involSeries where
  ρ := involSeries.radius
  radFilter := atTop
  a := involSaddleAReal
  b := involSaddleBReal
  δ := involSaddleDeltaReal
  hp := involFun_hasFPowerSeriesAt_zero
  radius_eq := rfl
  radius_pos := by
    simpa [involSeries] using involFun_hasFPowerSeriesAt_zero.radius_pos
  rad_neBot := by infer_instance
  r_pos := eventually_gt_atTop (0 : ℝ)
  differentiableOn := invol_differentiableOn_eventually
  f_pos := invol_f_pos_eventually
  b_pos := invol_b_pos_eventually
  δ_pos := invol_delta_pos_eventually
  δ_le_pi := invol_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := invol_delta_sqrt_b_tendsto_atTop
  local_uniform := invol_local_uniform
  tail_uniform := invol_tail_uniform

def involHAdmissibleSaddleSequence : SaddleSequence involHAdmissible where
  r := involSaddleRadius
  tendsTo := by
    simpa [involHAdmissible] using involSaddleRadius_tendsto_atTop
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change involSaddleAReal (involSaddleRadius n) = (n : ℝ)
      exact involSaddleAReal_radius n

end InvolutionHAdmissible
end
end

section
/-!
# Second-order saddle core definitions

This file defines the universal Gaussian correction polynomial and the scalar
second-order correction appearing after integrating its even moments.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

lemma saddleSecondPoly_quarticCoeff_norm_le_scale
    {b b3 b4 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖ ≤
      (1 / 24 : ℝ) * saddleCorrectionScale b b3 b4 r := by
  have hb2pos : 0 < (b r) ^ 2 := sq_pos_of_pos hb
  have hb3nonneg : 0 ≤ (b3 r) ^ 2 / (b r) ^ 3 := by
    exact div_nonneg (sq_nonneg _) (by positivity)
  calc
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖
        = |b4 r| / (24 * (b r) ^ 2) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 24 : ℝ) * (|b4 r| / (b r) ^ 2) := by ring
    _ ≤ (1 / 24 : ℝ) * (|b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb3nonneg)
            (by norm_num)
    _ = (1 / 24 : ℝ) * saddleCorrectionScale b b3 b4 r := by rfl

lemma saddleSecondPoly_sexticCoeff_norm_le_scale
    {b b3 b4 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖ ≤
      (1 / 72 : ℝ) * saddleCorrectionScale b b3 b4 r := by
  have hb2nonneg : 0 ≤ |b4 r| / (b r) ^ 2 := by
    exact div_nonneg (abs_nonneg _) (sq_nonneg _)
  calc
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖
        = (b3 r) ^ 2 / (72 * (b r) ^ 3) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 72 : ℝ) * ((b3 r) ^ 2 / (b r) ^ 3) := by ring
    _ ≤ (1 / 72 : ℝ) * (|b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hb2nonneg)
            (by norm_num)
    _ = (1 / 72 : ℝ) * saddleCorrectionScale b b3 b4 r := by rfl

private lemma gaussian_weighted_integrable_zero :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) =
      (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))

private lemma gaussian_weighted_integrable_four :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 4) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 4) =
      (fun x : ℝ => x ^ 4 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 4))

private lemma gaussian_weighted_integrable_six :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6) =
      (fun x : ℝ => x ^ 6 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 6))

private lemma gaussian_complex_integrable_zero :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2)) := by
  simpa using (gaussian_weighted_integrable_zero.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_four :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) := by
  simpa using (gaussian_weighted_integrable_four.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_six :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) := by
  simpa using (gaussian_weighted_integrable_six.ofReal (𝕜 := ℂ))

/-- The odd cubic Gaussian moment vanishes on every symmetric window. -/
lemma gaussian_window_weighted_moment_three_eq_zero (L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3) = 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3
  have hcomp : (∫ x in -L..L, g (-x)) = ∫ x in -L..L, g x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := g) (a := -L) (b := L))
  have hodd : (fun x : ℝ => g (-x)) = fun x : ℝ => -g x := by
    funext x
    simp [g]
    ring
  rw [hodd] at hcomp
  rw [intervalIntegral.integral_neg] at hcomp
  have hzero : (∫ x in -L..L, g x) = -(∫ x in -L..L, g x) := hcomp.symm
  have htwo : (2 : ℂ) * (∫ x in -L..L, g x) = 0 := by
    calc
      (2 : ℂ) * (∫ x in -L..L, g x) =
          (∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by ring
      _ = -(∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by
            nth_rw 1 [hzero]
      _ = 0 := by ring
  simpa [g] using (mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

private lemma gaussian_complex_weighted_moment_four :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) =
      (3 * Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) =
        (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 4 : ℝ) : ℂ)) by
          funext x
          simp]
    rw [integral_complex_ofReal
      (f := fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 4)
      (μ := (volume : Measure ℝ))]
    exact_mod_cast gaussian_weighted_moment_four

private lemma gaussian_complex_weighted_moment_six :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) =
      (15 * Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) =
        (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 6 : ℝ) : ℂ)) by
          funext x
          simp]
    rw [integral_complex_ofReal
      (f := fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6)
      (μ := (volume : Measure ℝ))]
    exact_mod_cast gaussian_weighted_moment_six

/-- The scalar correction is exactly the normalized quartic and sextic Gaussian moments. -/
theorem saddleCorrection_eq_gaussian_even_moments (b b3 b4 : ℝ → ℝ) (r : ℝ) :
    (saddleCorrection b b3 b4 r : ℂ) =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
          ((((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) := by
  rw [gaussian_complex_weighted_moment_four, gaussian_complex_weighted_moment_six]
  simp [saddleCorrection]
  have hsqrtπ_ne : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsqrt2_ne : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hsqrtπ_ne, hsqrt2_ne]
  ring_nf

/--
Symmetric-window version of the polynomial expansion.  The cubic contribution
vanishes exactly on `[-L,L]`.
-/
theorem gaussian_window_integral_saddleSecondPoly
    (b b3 b4 : ℝ → ℝ) (r L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
        saddleSecondPoly b b3 b4 r x) =
      (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) +
        ((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
        ((((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) := by
  let A : ℂ := Complex.I * ((b3 r : ℂ) / (6 * (Real.sqrt (b r) : ℂ) ^ 3))
  let D : ℂ := (b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)
  let E : ℂ := (((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)
  let F0 : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2)
  let F3 : ℝ → ℂ := fun x => A * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)
  let F4 : ℝ → ℂ := fun x => D * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  let F6 : ℝ → ℂ := fun x => E * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  have hpoly :
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * saddleSecondPoly b b3 b4 r x) =
        fun x : ℝ => (F0 - F3 + F4 - F6) x := by
    funext x
    simp [F0, F3, F4, F6, saddleSecondPoly, A, D, E]
    ring
  rw [hpoly]
  have hF0 : IntervalIntegrable F0 volume (-L) L := by
    have hcont : Continuous F0 := by
      unfold F0
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF3 : IntervalIntegrable F3 volume (-L) L := by
    have hcont : Continuous F3 := by
      unfold F3
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF4 : IntervalIntegrable F4 volume (-L) L := by
    have hcont : Continuous F4 := by
      unfold F4
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF6 : IntervalIntegrable F6 volume (-L) L := by
    have hcont : Continuous F6 := by
      unfold F6
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF03 : IntervalIntegrable (fun x : ℝ => F0 x - F3 x) volume (-L) L := hF0.sub hF3
  have hF034 : IntervalIntegrable (fun x : ℝ => F0 x - F3 x + F4 x) volume (-L) L :=
    hF03.add hF4
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [intervalIntegral.integral_sub hF034 hF6]
  rw [intervalIntegral.integral_add hF03 hF4]
  rw [intervalIntegral.integral_sub hF0 hF3]
  simp only [F0, F3, F4, F6]
  have hAeval :
      (∫ x in -L..L, A * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)) =
        A * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3 := by
    exact intervalIntegral.integral_const_mul A
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)
  have hDeval :
      (∫ x in -L..L, D * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) =
        D * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4 := by
    exact intervalIntegral.integral_const_mul D
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  have hEeval :
      (∫ x in -L..L, E * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) =
        E * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6 := by
    exact intervalIntegral.integral_const_mul E
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  rw [hAeval, hDeval, hEeval, gaussian_window_weighted_moment_three_eq_zero]
  simp [A, D, E]

/-- Expanding symmetric windows exhaust an integrable function on the line. -/
lemma intervalIntegral_tendsto_integral_symmetric
    {g : ℝ → ℂ} (hg : Integrable g) {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun n : ℕ => ∫ x in -(L n)..(L n), g x)
      atTop (𝓝 (∫ x : ℝ, g x)) := by
  simpa using
    (intervalIntegral_tendsto_integral (μ := volume) hg
      (tendsto_neg_atTop_atBot.comp hL) hL)

/-- Fourth weighted Gaussian windows converge to the full fourth moment. -/
lemma gaussian_window_weighted_moment_four_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_four hL

/-- Sixth weighted Gaussian windows converge to the full sixth moment. -/
lemma gaussian_window_weighted_moment_six_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_six hL

/-- A crude one-sided Gaussian tail bound, enough for relative saddle-window estimates. -/
lemma gaussian_tail_Ioi_le_exp {L : ℝ} (hL : 1 ≤ L) :
    (∫ x in Set.Ioi L, Real.exp (-(x ^ 2) / 2)) ≤
      Real.exp (-(L ^ 2) / 2) := by
  have hderiv : ∀ x ∈ Set.Ici L,
      HasDerivAt (fun y : ℝ => -Real.exp (-(y ^ 2) / 2))
        (x * Real.exp (-(x ^ 2) / 2)) x := by
    intro x _hx
    have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
      convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
      ring
    have h2 := h1.exp.neg
    convert h2 using 1
    ring
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi L) := by
    have hbase : Integrable (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    convert hbase.integrableOn using 1
    funext x
    ring_nf
  have htop : Tendsto (fun y : ℝ => -Real.exp (-(y ^ 2) / 2)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun y : ℝ => -(y ^ 2) / 2) atTop atBot := by
      have hpow : Tendsto (fun y : ℝ => y ^ 2) atTop atTop :=
        tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
      have hmul : Tendsto (fun y : ℝ => (-(1 / 2 : ℝ)) * y ^ 2) atTop atBot :=
        (tendsto_const_mul_atBot_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0)).mpr hpow
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hexp : Tendsto (fun y : ℝ => Real.exp (-(y ^ 2) / 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hsq
    simpa using hexp.neg
  have hxeq : (∫ x in Set.Ioi L, x * Real.exp (-(x ^ 2) / 2)) =
      Real.exp (-(L ^ 2) / 2) := by
    convert integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htop using 1
    ring
  have hleftint : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Set.Ioi L) := by
    have hbase : Integrable (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    convert hbase.integrableOn using 1
    funext x
    ring_nf
  have hmono : (∫ x in Set.Ioi L, Real.exp (-(x ^ 2) / 2)) ≤
      ∫ x in Set.Ioi L, x * Real.exp (-(x ^ 2) / 2) := by
    refine setIntegral_mono_on hleftint hint measurableSet_Ioi ?_
    intro x hx
    have hxL : L < x := hx
    have hx1 : 1 ≤ x := le_trans hL (le_of_lt hxL)
    have hnon : 0 ≤ Real.exp (-(x ^ 2) / 2) := (Real.exp_pos _).le
    calc
      Real.exp (-(x ^ 2) / 2) = 1 * Real.exp (-(x ^ 2) / 2) := by simp
      _ ≤ x * Real.exp (-(x ^ 2) / 2) :=
            mul_le_mul_of_nonneg_right hx1 hnon
  simpa [hxeq] using hmono

/--
The normalized zeroth Gaussian window differs from `1` by at most a constant
times the one-sided Gaussian boundary exponential.
-/
lemma gaussian_window_zero_error_norm_le_exp {L : ℝ} (hL : 1 ≤ L) :
    ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) - 1‖
      ≤ (2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(L ^ 2) / 2) := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2)
  let tail : ℂ := ∫ x in Set.Ioi L, g x
  let leftTail : ℂ := ∫ x in Set.Iic (-L), g x
  let window : ℂ := ∫ x in -L..L, g x
  let invG : ℂ := (1 / Real.sqrt (2 * Real.pi) : ℂ)
  have hLnonneg : 0 ≤ L := le_trans zero_le_one hL
  have hg : Integrable g := by
    simpa [g] using gaussian_complex_integrable_zero
  have hleftInt : IntegrableOn g (Set.Iic (-L)) := hg.integrableOn
  have hrightFromLeft : IntegrableOn g (Set.Ioi (-L)) := hg.integrableOn
  have hrightInt : IntegrableOn g (Set.Ioi L) := hg.integrableOn
  have hsplitFull :
      leftTail + (∫ x in Set.Ioi (-L), g x) = ∫ x : ℝ, g x := by
    simpa [leftTail] using
      (intervalIntegral.integral_Iic_add_Ioi (f := g) (b := -L) hleftInt hrightFromLeft)
  have hsplitRight :
      window + tail = ∫ x in Set.Ioi (-L), g x := by
    simpa [window, tail] using
      (intervalIntegral.integral_interval_add_Ioi
        (f := g) (a := -L) (b := L) hrightFromLeft hrightInt)
  have hfull :
      (∫ x : ℝ, g x) = leftTail + window + tail := by
    calc
      (∫ x : ℝ, g x) = leftTail + (∫ x in Set.Ioi (-L), g x) := hsplitFull.symm
      _ = leftTail + (window + tail) := by rw [← hsplitRight]
      _ = leftTail + window + tail := by ring
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hinv_full : invG * (∫ x : ℝ, g x) = 1 := by
    rw [gaussian_integral_half]
    change (1 / (Real.sqrt (2 * Real.pi) : ℂ)) *
        (Real.sqrt (2 * Real.pi) : ℂ) = 1
    field_simp [Complex.ofReal_ne_zero.mpr hsqrt_pos.ne']
  have hdiff :
      invG * window - 1 = -invG * (leftTail + tail) := by
    rw [← hinv_full, hfull]
    ring
  have hrightNorm :
      ‖tail‖ ≤ Real.exp (-(L ^ 2) / 2) := by
    calc
      ‖tail‖ ≤ ∫ x in Set.Ioi L, ‖g x‖ := by
        simpa [tail] using
          (norm_integral_le_integral_norm
            (f := fun x : ℝ => g x) (μ := volume.restrict (Set.Ioi L)))
      _ = ∫ x in Set.Ioi L, Real.exp (-(x ^ 2) / 2) := by
        apply integral_congr_ae
        refine ae_of_all _ ?_
        intro x
        simp [g, Complex.norm_exp, sq]
      _ ≤ Real.exp (-(L ^ 2) / 2) := gaussian_tail_Ioi_le_exp hL
  have hleftEq : leftTail = tail := by
    have hcomp :
        (∫ x in Set.Iic (-L), g (-x)) = ∫ x in Set.Ioi L, g x := by
      simpa only [neg_neg] using (integral_comp_neg_Iic (c := -L) (f := g))
    have heven :
        (∫ x in Set.Iic (-L), g (-x)) = ∫ x in Set.Iic (-L), g x := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x _hx
      simp [g]
    simpa [leftTail, tail] using heven.symm.trans hcomp
  have hleftNorm :
      ‖leftTail‖ ≤ Real.exp (-(L ^ 2) / 2) := by
    simpa [hleftEq] using hrightNorm
  calc
    ‖invG * window - 1‖ = ‖-invG * (leftTail + tail)‖ := by rw [hdiff]
    _ ≤ ‖invG‖ * (‖leftTail‖ + ‖tail‖) := by
      rw [norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖invG‖ *
        (Real.exp (-(L ^ 2) / 2) + Real.exp (-(L ^ 2) / 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hleftNorm hrightNorm) (norm_nonneg _)
    _ = (2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(L ^ 2) / 2) := by
      have hinv_norm : ‖invG‖ = 1 / Real.sqrt (2 * Real.pi) := by
        dsimp [invG]
        rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hsqrt_pos]
      rw [hinv_norm]
      ring

end
end

section
/-!
# Second-order H-admissible wrapper

This is a clean add-on to the first-order `HAdmissible` interface.  It records
the third and fourth logarithmic saddle derivatives, the robust correction
scale, and the local/tail hypotheses used by the second-order saddle layer.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

private lemma complex_isLittleO_of_norm_div_tendsto_zero
    (u : ℕ → ℂ) (c : ℕ → ℝ)
    (hcpos : ∀ᶠ n in atTop, 0 < c n)
    (h : Tendsto (fun n : ℕ => ‖u n‖ / c n) atTop (𝓝 0)) :
    u =o[atTop] (fun n : ℕ => (c n : ℂ)) := by
  rw [isLittleO_iff_tendsto']
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Tendsto.congr' ?_ h
    filter_upwards [hcpos] with n hcn
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcn]
  · filter_upwards [hcpos] with n hcn hzero
    exact (hcn.ne' (Complex.ofReal_eq_zero.mp hzero)).elim

private lemma second_tail_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        saddleJt f hr.r (HAdmissible.Δ hf hr) n)
      =o[atTop]
    (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
  rcases h2.tail_second_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
  let K : ℝ := ‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hδ_nonneg : ∀ᶠ n in atTop, 0 ≤ HAdmissible.Δ hf hr n := by
    filter_upwards [hr.tendsTo.eventually hf.δ_pos] with n hδn
    exact hδn.le
  have hδπ : ∀ᶠ n in atTop, HAdmissible.Δ hf hr n ≤ Real.pi := by
    simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_le_pi
  have hE_nonneg_seq : ∀ᶠ n in atTop, 0 ≤ E (hr.r n) := by
    simpa using hr.tendsTo.eventually hE_nonneg
  have htailSeq :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        HAdmissible.Δ hf hr n ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
    filter_upwards [hr.tendsTo.eventually htail] with n htailn θ hδθ hθπ
    simpa [HAdmissible.Δ, saddleG] using htailn n θ hδθ hθπ
  have hCpos : ∀ᶠ n in atTop, 0 < h2.corrScale (hr.r n) := by
    simpa using hr.tendsTo.eventually h2.corrScale_pos
  have hdecaySeq :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
            E (hr.r n) / h2.corrScale (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B] using hdecay.comp hr.tendsTo
  have hupper :
      Tendsto
        (fun n : ℕ =>
          K * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
            E (hr.r n) / h2.corrScale (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hdecaySeq.const_mul K
  have hbound :
      ∀ᶠ n in atTop,
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ /
            h2.corrScale (hr.r n) ≤
          K * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
            E (hr.r n) / h2.corrScale (hr.r n)) := by
    filter_upwards [hBpos, hδ_nonneg, hδπ, hE_nonneg_seq, htailSeq, hCpos] with
      n hBn hδn hδπn hEn htailn hCn
    have hJ : ‖saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ ≤ K * E (hr.r n) := by
      simpa [saddleJt, saddleG, K] using
        saddleJtAt_norm_le_of_tail_bound f (hr.r n) (HAdmissible.Δ hf hr n)
          (E (hr.r n)) n hδn hδπn hEn
          (fun θ hδθ hθπ => htailn θ hδθ hθπ)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) :=
      Real.sqrt_nonneg _
    have hnorm :
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ ≤
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * (K * E (hr.r n)) := by
      calc
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖
            =
              Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                ‖saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg hsqrt_nonneg]
        _ ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
              (K * E (hr.r n)) :=
              mul_le_mul_of_nonneg_left hJ hsqrt_nonneg
    have hdiv := div_le_div_of_nonneg_right hnorm hCn.le
    calc
      ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ / h2.corrScale (hr.r n)
          ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
              (K * E (hr.r n)) / h2.corrScale (hr.r n) := hdiv
      _ = K * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
              E (hr.r n) / h2.corrScale (hr.r n)) := by ring
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤ ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ /
            h2.corrScale (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (norm_nonneg _) hCn.le
  have hnormdiv :
      Tendsto
        (fun n : ℕ =>
          ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ /
            h2.corrScale (hr.r n))
        atTop (𝓝 0) :=
    squeeze_zero' hnonneg hbound hupper
  exact complex_isLittleO_of_norm_div_tendsto_zero _ _ hCpos hnormdiv

private lemma coeff_ratio_eq_scaled_saddleJ_eventually
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n)
      =ᶠ[atTop]
    (fun n : ℕ =>
      (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
          saddleJt f hr.r (HAdmissible.Δ hf hr) n)) := by
  have hrpos : ∀ᶠ n in atTop, 0 < hr.r n := by
    simpa using hr.tendsTo.eventually hf.r_pos
  have hdiff :
      ∀ᶠ n in atTop,
        DifferentiableOn ℂ f (Metric.closedBall 0 (hr.r n)) := by
    simpa using hr.tendsTo.eventually hf.differentiableOn
  have hfnz : ∀ᶠ n in atTop, f (hr.r n : ℂ) ≠ 0 := by
    filter_upwards [hr.tendsTo.eventually hf.f_pos] with n hpos
    exact f_ne_zero_of_re_pos hpos
  have hleft :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (-Real.pi) (-(HAdmissible.Δ hf hr n)) := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (-Real.pi) (-(HAdmissible.Δ hf hr n)) hrn.le hdn
  have hcenter :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (-(HAdmissible.Δ hf hr n)) (HAdmissible.Δ hf hr n) := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (-(HAdmissible.Δ hf hr n)) (HAdmissible.Δ hf hr n) hrn.le hdn
  have hright :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (HAdmissible.Δ hf hr n) Real.pi := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (HAdmissible.Δ hf hr n) Real.pi hrn.le hdn
  have Hsplit :
      ∀ᶠ n in atTop,
        p.coeff n =
          saddlePref f hr.r n *
            (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
              saddleJt f hr.r (HAdmissible.Δ hf hr) n) :=
    eventually_coeff_eq_saddle_split
      hr.r (HAdmissible.Δ hf hr) hf.hp hrpos hdiff hfnz hleft hcenter hright
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have Hnz :
      ∀ᶠ n in atTop, saddleScale f hr.r (HAdmissible.B hf hr) n ≠ 0 := by
    filter_upwards [hrpos, hr.tendsTo.eventually hf.f_pos, hBpos] with n hrn hfn hBn
    exact saddleScale_nonzero_of_pos f hr.r (HAdmissible.B hf hr) n hrn hfn hBn
  filter_upwards [Hsplit, Hnz] with n hsplit hnz
  rw [hsplit]
  dsimp [saddleScale]
  have hS : (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) ≠ 0 := by
    intro hzero
    apply hnz
    simp [hzero, saddleScale]
  have hpref : saddlePref f hr.r n ≠ 0 := by
    intro hpref_zero
    apply hnz
    simp [hpref_zero, saddleScale]
  field_simp [hpref, hS]

private lemma second_central_local_error_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJc f hr.r (HAdmissible.Δ hf hr) n -
        (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          ∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            Complex.exp (-(x ^ 2) / 2) *
              saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x)
      =o[atTop]
    (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
  let invG : ℂ := (1 / Real.sqrt (2 * Real.pi) : ℂ)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hRpos : ∀ᶠ n in atTop, 0 < hr.r n := by
    simpa using hr.tendsTo.eventually hf.r_pos
  have hδpos : ∀ᶠ n in atTop, 0 < HAdmissible.Δ hf hr n := by
    simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_pos
  have hdiff :
      ∀ᶠ n in atTop,
        DifferentiableOn ℂ f (Metric.closedBall 0 (hr.r n)) := by
    simpa using hr.tendsTo.eventually hf.differentiableOn
  have hsaddle : ∀ᶠ n in atTop, hf.a (hr.r n) = (n : ℝ) := hr.saddle_eq
  have hCpos : ∀ᶠ n in atTop, 0 < h2.corrScale (hr.r n) := by
    simpa using hr.tendsTo.eventually h2.corrScale_pos
  have hlocalSeq :
      Tendsto
        (fun n : ℕ =>
          (∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleLocalRatio f hf.a hf.b (hr.r n)
                (x / Real.sqrt (HAdmissible.B hf hr n)) -
                saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x)‖) /
            h2.corrScale (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B, HAdmissible.Δ] using h2.local_second_L1.comp hr.tendsTo
  have hupper :
      Tendsto
        (fun n : ℕ =>
          ‖invG‖ *
            ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              ‖Complex.exp (-(x ^ 2) / 2) *
                (saddleLocalRatio f hf.a hf.b (hr.r n)
                  (x / Real.sqrt (HAdmissible.B hf hr n)) -
                  saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x)‖) /
              h2.corrScale (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hlocalSeq.const_mul ‖invG‖
  have hbound :
      ∀ᶠ n in atTop,
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            invG *
              ∫ x in
                -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                  (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                Complex.exp (-(x ^ 2) / 2) *
                  saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x‖ /
            h2.corrScale (hr.r n) ≤
          ‖invG‖ *
            ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              ‖Complex.exp (-(x ^ 2) / 2) *
                (saddleLocalRatio f hf.a hf.b (hr.r n)
                  (x / Real.sqrt (HAdmissible.B hf hr n)) -
                  saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x)‖) /
              h2.corrScale (hr.r n)) := by
    filter_upwards [hBpos, hRpos, hδpos, hdiff, hsaddle, hCpos] with
      n hBn hRn hδn hdiffn han hCn
    let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
    let G : ℝ → ℂ := fun x => saddleG f hr.r n (x / Real.sqrt (HAdmissible.B hf hr n))
    let P : ℝ → ℂ := fun x =>
      Complex.exp (-(x ^ 2) / 2) *
        saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x
    let Err : ℝ → ℂ := fun x =>
      Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio f hf.a hf.b (hr.r n)
          (x / Real.sqrt (HAdmissible.B hf hr n)) -
          saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x)
    have hscaled :
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJc f hr.r (HAdmissible.Δ hf hr) n =
          invG * ∫ x in -L..L, G x := by
      simpa [L, G, invG] using
        saddleJc_eq_integral_scaled f hr.r (HAdmissible.Δ hf hr)
          (HAdmissible.B hf hr) n hBn
    have hGcont : Continuous G := by
      have h0 := saddleGAt_continuous_of_differentiableOn_closedBall
        f (hr.r n) n hRn.le hdiffn
      have hdiv : Continuous fun x : ℝ => x / Real.sqrt (HAdmissible.B hf hr n) := by
        fun_prop
      simpa [G, saddleG] using h0.comp hdiv
    have hGint : IntervalIntegrable G volume (-L) L :=
      hGcont.intervalIntegrable _ _
    have hPcont : Continuous P := by
      unfold P saddleSecondPoly
      fun_prop
    have hPint : IntervalIntegrable P volume (-L) L :=
      hPcont.intervalIntegrable _ _
    have hsub :
        (∫ x in -L..L, G x) - (∫ x in -L..L, P x) =
          ∫ x in -L..L, G x - P x := by
      rw [intervalIntegral.integral_sub hGint hPint]
    have hErr :
        (fun x : ℝ => G x - P x) = fun x : ℝ => Err x := by
      funext x
      have hGx :
          G x =
            Complex.exp (-(x ^ 2) / 2) *
              saddleLocalRatio f hf.a hf.b (hr.r n)
                (x / Real.sqrt (HAdmissible.B hf hr n)) := by
        simpa [G, saddleG, HAdmissible.B] using
          saddleGAt_eq_gaussian_mul_saddleLocalRatio
            f hf.a hf.b (hr.r n) x n hBn han
      rw [hGx]
      simp [P, Err]
      ring
    have hdiff_eq :
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            invG * (∫ x in -L..L, P x) =
          invG * ∫ x in -L..L, Err x := by
      rw [hscaled]
      rw [← mul_sub]
      rw [hsub]
      rw [hErr]
    have hLnonneg : 0 ≤ L := by
      exact mul_nonneg hδn.le (Real.sqrt_nonneg _)
    have hle : -L ≤ L := by linarith
    have hnormInt :
        ‖∫ x in -L..L, Err x‖ ≤
          ∫ x in -L..L, ‖Err x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hle
    have hnorm :
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            invG * (∫ x in -L..L, P x)‖ ≤
          ‖invG‖ * (∫ x in -L..L, ‖Err x‖) := by
      rw [hdiff_eq]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hnormInt (norm_nonneg _)
    have hdiv := div_le_div_of_nonneg_right hnorm hCn.le
    calc
      ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJc f hr.r (HAdmissible.Δ hf hr) n -
          invG * (∫ x in -L..L, P x)‖ / h2.corrScale (hr.r n)
          ≤ ‖invG‖ * (∫ x in -L..L, ‖Err x‖) / h2.corrScale (hr.r n) := hdiv
      _ = ‖invG‖ *
            ((∫ x in -L..L, ‖Err x‖) / h2.corrScale (hr.r n)) := by ring
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤
          ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
                saddleJc f hr.r (HAdmissible.Δ hf hr) n -
              invG *
                ∫ x in
                  -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                    (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                  Complex.exp (-(x ^ 2) / 2) *
                    saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x‖ /
              h2.corrScale (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (norm_nonneg _) hCn.le
  have hnormdiv :
      Tendsto
        (fun n : ℕ =>
          ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
                saddleJc f hr.r (HAdmissible.Δ hf hr) n -
              invG *
                ∫ x in
                  -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                    (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                  Complex.exp (-(x ^ 2) / 2) *
                    saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x‖ /
              h2.corrScale (hr.r n))
        atTop (𝓝 0) :=
    squeeze_zero' hnonneg hbound hupper
  exact complex_isLittleO_of_norm_div_tendsto_zero _ _ hCpos hnormdiv

private lemma gaussian_boundary_exp_div_corr_tendsto_zero
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
          h2.corrScale (hr.r n))
      atTop (𝓝 0) := by
  set_option backward.isDefEq.respectTransparency false in
    rcases h2.tail_second_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
    have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
      simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
    have hδpos : ∀ᶠ n in atTop, 0 < HAdmissible.Δ hf hr n := by
      simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_pos
    have hδπ : ∀ᶠ n in atTop, HAdmissible.Δ hf hr n ≤ Real.pi := by
      simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_le_pi
    have hsaddle : ∀ᶠ n in atTop, hf.a (hr.r n) = (n : ℝ) := hr.saddle_eq
    have hCpos : ∀ᶠ n in atTop, 0 < h2.corrScale (hr.r n) := by
      simpa using hr.tendsTo.eventually h2.corrScale_pos
    have hE_nonneg_seq : ∀ᶠ n in atTop, 0 ≤ E (hr.r n) := by
      simpa using hr.tendsTo.eventually hE_nonneg
    have htailSeq :
        ∀ᶠ n in atTop, ∀ θ : ℝ,
          HAdmissible.Δ hf hr n ≤ |θ| → |θ| ≤ Real.pi →
            ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
      filter_upwards [hr.tendsTo.eventually htail] with n htailn θ hδθ hθπ
      simpa [HAdmissible.Δ, saddleG] using htailn n θ hδθ hθπ
    have hlocal :
        ∀ᶠ n in atTop, ∀ θ : ℝ,
          |θ| ≤ HAdmissible.Δ hf hr n →
            ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ ≤ (1 / 2 : ℝ) := by
      simpa [HAdmissible.Δ] using
        hr.tendsTo.eventually (hf.local_uniform (1 / 2) (by norm_num))
    have hLtop :
        Tendsto
          (fun n : ℕ => HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))
          atTop atTop := by
      simpa [HAdmissible.B, HAdmissible.Δ] using
        hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
    have hsqrtFactor_ge_one :
        ∀ᶠ n in atTop, 1 ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) := by
      have hLπ : ∀ᶠ n in atTop,
          Real.pi ≤ HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n) :=
        hLtop.eventually_ge_atTop Real.pi
      filter_upwards [hLπ, hδπ, hBpos] with n hLn hδπn hBn
      have hsqrtB_nonneg : 0 ≤ Real.sqrt (HAdmissible.B hf hr n) := Real.sqrt_nonneg _
      have hπsqrt :
          Real.pi * Real.sqrt (HAdmissible.B hf hr n) ≥ Real.pi := by
        calc
          Real.pi ≤ HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n) := hLn
          _ ≤ Real.pi * Real.sqrt (HAdmissible.B hf hr n) :=
                mul_le_mul_of_nonneg_right hδπn hsqrtB_nonneg
      have hsqrtB_ge_one : 1 ≤ Real.sqrt (HAdmissible.B hf hr n) := by
        have hpi_pos : 0 < Real.pi := Real.pi_pos
        exact (le_mul_iff_one_le_right hpi_pos).mp (by simpa [ge_iff_le] using hπsqrt)
      have hB_ge_one : 1 ≤ HAdmissible.B hf hr n := by
        have hs := Real.sq_sqrt hBn.le
        nlinarith [sq_nonneg (Real.sqrt (HAdmissible.B hf hr n)), hsqrtB_ge_one, hs]
      have harg : 1 ≤ 2 * Real.pi * HAdmissible.B hf hr n := by
        nlinarith [Real.pi_gt_three, hB_ge_one]
      simpa using (Real.one_le_sqrt.mpr harg)
    have hdecaySeq :
        Tendsto
          (fun n : ℕ =>
            Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
              h2.corrScale (hr.r n))
          atTop (𝓝 0) := by
      simpa [HAdmissible.B] using hdecay.comp hr.tendsTo
    have hupper :
        Tendsto
          (fun n : ℕ =>
            2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
              h2.corrScale (hr.r n)))
          atTop (𝓝 0) := by
      simpa using hdecaySeq.const_mul 2
    have hbound :
        ∀ᶠ n in atTop,
          Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h2.corrScale (hr.r n) ≤
            2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
              h2.corrScale (hr.r n)) := by
      filter_upwards [hBpos, hδpos, hδπ, hsaddle, hCpos, hE_nonneg_seq, htailSeq,
        hlocal, hsqrtFactor_ge_one] with
        n hBn hδn hδπn han hCn hEn htailn hlocaln hsqrt_ge_one
      let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
      let θ : ℝ := HAdmissible.Δ hf hr n
      have hsqrt_pos : 0 < Real.sqrt (HAdmissible.B hf hr n) :=
        Real.sqrt_pos.mpr hBn
      have hθeq : L / Real.sqrt (HAdmissible.B hf hr n) = θ := by
        simp [L, θ, div_eq_mul_inv, hsqrt_pos.ne']
      have htheta_abs : |θ| = θ := abs_of_pos hδn
      have hratio_close :
          ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ ≤ (1 / 2 : ℝ) := by
        exact hlocaln θ (by simp [htheta_abs, θ])
      have hratio_lower :
          (1 / 2 : ℝ) ≤
            ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by
        have hone :
            ‖(1 : ℂ)‖ ≤
              ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ +
                ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by
          calc
            ‖(1 : ℂ)‖ =
                ‖-(saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1) +
                  saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by ring_nf
            _ ≤ ‖-(saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1)‖ +
                  ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ :=
                  norm_add_le _ _
            _ = ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ +
                  ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by rw [norm_neg]
        norm_num at hone
        linarith
      have hG :
          saddleG f hr.r n θ =
            Complex.exp (-(L ^ 2) / 2) *
              saddleLocalRatio f hf.a hf.b (hr.r n) θ := by
        rw [← hθeq]
        simpa [L, saddleG, HAdmissible.B] using
          saddleGAt_eq_gaussian_mul_saddleLocalRatio
            f hf.a hf.b (hr.r n) L n hBn han
      have hGnorm :
          ‖saddleG f hr.r n θ‖ =
            Real.exp (-(L ^ 2) / 2) *
              ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by
        rw [hG, norm_mul]
        have hnormexp :
            ‖Complex.exp (-(L ^ 2) / 2)‖ = Real.exp (-(L ^ 2) / 2) := by
          simp [Complex.norm_exp, sq]
        rw [hnormexp]
      have htail_at : ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
        exact htailn θ (by simp [θ, htheta_abs]) (by simpa [θ, htheta_abs] using hδπn)
      have hexp_nonneg : 0 ≤ Real.exp (-(L ^ 2) / 2) := (Real.exp_pos _).le
      have hexp_le : Real.exp (-(L ^ 2) / 2) ≤ 2 * E (hr.r n) := by
        have hhalf :
            Real.exp (-(L ^ 2) / 2) * (1 / 2 : ℝ) ≤ E (hr.r n) := by
          calc
            Real.exp (-(L ^ 2) / 2) * (1 / 2 : ℝ)
                ≤ Real.exp (-(L ^ 2) / 2) *
                    ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ :=
                      mul_le_mul_of_nonneg_left hratio_lower hexp_nonneg
            _ = ‖saddleG f hr.r n θ‖ := by rw [hGnorm]
            _ ≤ E (hr.r n) := htail_at
        nlinarith
      have hdiv := div_le_div_of_nonneg_right hexp_le hCn.le
      calc
        Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
            h2.corrScale (hr.r n)
            = Real.exp (-(L ^ 2) / 2) / h2.corrScale (hr.r n) := by simp [L]
        _ ≤ 2 * E (hr.r n) / h2.corrScale (hr.r n) := hdiv
        _ ≤ 2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
              h2.corrScale (hr.r n)) := by
            have hEdiv_nonneg : 0 ≤ E (hr.r n) / h2.corrScale (hr.r n) :=
              div_nonneg hEn hCn.le
            have hmul :
                E (hr.r n) / h2.corrScale (hr.r n) ≤
                  Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                    (E (hr.r n) / h2.corrScale (hr.r n)) := by
              simpa using
                mul_le_mul_of_nonneg_right hsqrt_ge_one hEdiv_nonneg
            calc
              2 * E (hr.r n) / h2.corrScale (hr.r n)
                  = 2 * (E (hr.r n) / h2.corrScale (hr.r n)) := by ring
              _ ≤ 2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                    (E (hr.r n) / h2.corrScale (hr.r n))) := by nlinarith
              _ = 2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                    E (hr.r n) / h2.corrScale (hr.r n)) := by ring
    have hnonneg :
        ∀ᶠ n in atTop,
          0 ≤
            Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h2.corrScale (hr.r n) := by
      filter_upwards [hCpos] with n hCn
      exact div_nonneg (Real.exp_pos _).le (le_of_lt hCn)
    exact squeeze_zero' hnonneg hbound hupper

private lemma second_window_zero_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            Complex.exp (-(x ^ 2) / 2)) -
        1)
      =o[atTop]
    (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
  have hCpos : ∀ᶠ n in atTop, 0 < h2.corrScale (hr.r n) := by
    simpa using hr.tendsTo.eventually h2.corrScale_pos
  have hLtop :
      Tendsto
        (fun n : ℕ => HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))
        atTop atTop := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hLone :
      ∀ᶠ n in atTop,
        1 ≤ HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n) :=
    hLtop.eventually_ge_atTop 1
  have hboundary := gaussian_boundary_exp_div_corr_tendsto_zero hf h2 hr
  have hupper :
      Tendsto
        (fun n : ℕ =>
          (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(HAdmissible.Δ hf hr n *
                Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h2.corrScale (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hboundary.const_mul (2 / Real.sqrt (2 * Real.pi))
  have hbound :
      ∀ᶠ n in atTop,
        ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
            (∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2)) -
            1‖ / h2.corrScale (hr.r n) ≤
          (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(HAdmissible.Δ hf hr n *
                Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h2.corrScale (hr.r n)) := by
    filter_upwards [hLone, hCpos] with n hLn hCn
    let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
    have hineq := gaussian_window_zero_error_norm_le_exp (L := L) hLn
    have hdiv := div_le_div_of_nonneg_right hineq hCn.le
    calc
      ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) - 1‖ /
          h2.corrScale (hr.r n)
          ≤ ((2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(L ^ 2) / 2)) /
              h2.corrScale (hr.r n) := hdiv
      _ = (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(L ^ 2) / 2) / h2.corrScale (hr.r n)) := by ring
      _ = (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(HAdmissible.Δ hf hr n *
                Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h2.corrScale (hr.r n)) := by simp [L]
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤
          ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
              (∫ x in
                -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                  (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                Complex.exp (-(x ^ 2) / 2)) -
              1‖ / h2.corrScale (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (norm_nonneg _) hCn.le
  have hnormdiv :
      Tendsto
        (fun n : ℕ =>
          ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
              (∫ x in
                -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                  (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                Complex.exp (-(x ^ 2) / 2)) -
              1‖ / h2.corrScale (hr.r n))
        atTop (𝓝 0) :=
    squeeze_zero' hnonneg hbound hupper
  exact complex_isLittleO_of_norm_div_tendsto_zero _ _ hCpos hnormdiv

private lemma second_window_quartic_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((h2.b4 (hr.r n) : ℂ) /
            (24 * (HAdmissible.B hf hr n : ℂ) ^ 2)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4))))
      =o[atTop]
    (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
  rcases h2.corrScale_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M4 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  let D : ℕ → ℂ := fun n =>
    (h2.b4 (hr.r n) : ℂ) / (24 * (HAdmissible.B hf hr n : ℂ) ^ 2)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h2.corrScale (hr.r n) := by
    simpa using hr.tendsTo.eventually h2.corrScale_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleCorrectionScale hf.b h2.b3 h2.b4 (hr.r n) ≤
          K * h2.corrScale (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM4_tendsto : Tendsto M4 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_four_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) :=
      tendsto_const_nhds
    simpa [M4] using hwin.sub hconst
  have hM4_little : M4 =o[atTop] (fun _ : ℕ => (1 : ℂ)) :=
    (isLittleO_one_iff ℂ).2 hM4_tendsto
  have hD_bigO : D =O[atTop] (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 24 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hDle :
        ‖D n‖ ≤ (1 / 24 : ℝ) *
          saddleCorrectionScale hf.b h2.b3 h2.b4 (hr.r n) := by
      simpa [D, HAdmissible.B] using
        saddleSecondPoly_quarticCoeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (r := hr.r n) hBn
    calc
      ‖D n‖ ≤ (1 / 24 : ℝ) *
          saddleCorrectionScale hf.b h2.b3 h2.b4 (hr.r n) := hDle
      _ ≤ (1 / 24 : ℝ) * (K * h2.corrScale (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 24 : ℝ) * K) * ‖(h2.corrScale (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  have hprod := hD_bigO.mul_isLittleO hM4_little
  have hscaled := hprod.const_mul_left (1 / Real.sqrt (2 * Real.pi) : ℂ)
  simpa [D, M4, L, mul_assoc] using hscaled

private lemma second_window_sextic_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((((h2.b3 (hr.r n)) ^ 2 : ℝ) : ℂ) /
            (72 * (HAdmissible.B hf hr n : ℂ) ^ 3)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6))))
      =o[atTop]
    (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
  rcases h2.corrScale_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M6 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  let E : ℕ → ℂ := fun n =>
    (((h2.b3 (hr.r n)) ^ 2 : ℝ) : ℂ) /
      (72 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h2.corrScale (hr.r n) := by
    simpa using hr.tendsTo.eventually h2.corrScale_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleCorrectionScale hf.b h2.b3 h2.b4 (hr.r n) ≤
          K * h2.corrScale (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM6_tendsto : Tendsto M6 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_six_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) :=
      tendsto_const_nhds
    simpa [M6] using hwin.sub hconst
  have hM6_little : M6 =o[atTop] (fun _ : ℕ => (1 : ℂ)) :=
    (isLittleO_one_iff ℂ).2 hM6_tendsto
  have hE_bigO : E =O[atTop] (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 72 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hEle :
        ‖E n‖ ≤ (1 / 72 : ℝ) *
          saddleCorrectionScale hf.b h2.b3 h2.b4 (hr.r n) := by
      simpa [E, HAdmissible.B] using
        saddleSecondPoly_sexticCoeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (r := hr.r n) hBn
    calc
      ‖E n‖ ≤ (1 / 72 : ℝ) *
          saddleCorrectionScale hf.b h2.b3 h2.b4 (hr.r n) := hEle
      _ ≤ (1 / 72 : ℝ) * (K * h2.corrScale (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 72 : ℝ) * K) * ‖(h2.corrScale (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  have hprod := hE_bigO.mul_isLittleO hM6_little
  have hscaled := hprod.const_mul_left (1 / Real.sqrt (2 * Real.pi) : ℂ)
  simpa [E, M6, L, mul_assoc] using hscaled

private lemma second_window_poly_integral_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            Complex.exp (-(x ^ 2) / 2) *
              saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x) -
        (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
  have h0 := second_window_zero_isLittleO hf h2 hr
  have h4 := second_window_quartic_isLittleO hf h2 hr
  have h6 := second_window_sextic_isLittleO hf h2 hr
  have hsum := h0.add (h4.sub h6)
  refine hsum.congr_left ?_
  intro n
  let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let invG : ℂ := (1 / Real.sqrt (2 * Real.pi) : ℂ)
  let W0 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)
  let W4 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4
  let W6 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6
  let F4 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4
  let F6 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6
  let D : ℂ := (h2.b4 (hr.r n) : ℂ) / (24 * (HAdmissible.B hf hr n : ℂ) ^ 2)
  let E : ℂ := (((h2.b3 (hr.r n)) ^ 2 : ℝ) : ℂ) /
    (72 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  have hwin :
      (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
          saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x) =
        W0 + D * W4 - E * W6 := by
    simpa [L, W0, W4, W6, D, E, HAdmissible.B] using
      gaussian_window_integral_saddleSecondPoly
        hf.b h2.b3 h2.b4 (hr.r n) L
  have hcorr :
      (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) =
        invG * (D * F4 - E * F6) := by
    simpa [invG, D, E, F4, F6, HAdmissible.B] using
      saddleCorrection_eq_gaussian_even_moments
        hf.b h2.b3 h2.b4 (hr.r n)
  calc
    ((invG * W0 - 1) + (invG * (D * (W4 - F4)) - invG * (E * (W6 - F6))))
        = invG * (W0 + D * W4 - E * W6) -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ)) := by
          rw [hcorr]
          ring
    _ = invG *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
            saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x) -
          (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ)) := by
          rw [hwin]
    _ =
        (1 / Real.sqrt (2 * Real.pi) : ℂ) *
            (∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) *
                saddleSecondPoly hf.b h2.b3 h2.b4 (hr.r n) x) -
          (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ)) := by
          simp [L, invG]

/-- Abstract second-order saddle ratio theorem. -/
theorem coeff_secondOrder_saddle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n -
        (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) :=
  by
    have hcentral := second_central_local_error_isLittleO hf h2 hr
    have hpoly := second_window_poly_integral_isLittleO hf h2 hr
    have htail := second_tail_isLittleO hf h2 hr
    have hcentralCorr :
        (fun n : ℕ =>
          (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ)))
          =o[atTop]
        (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
      have h := hcentral.add hpoly
      refine h.congr_left ?_
      intro n
      ring
    have hscaled :
        (fun n : ℕ =>
          (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
                saddleJt f hr.r (HAdmissible.Δ hf hr) n) -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ)))
          =o[atTop]
        (fun n : ℕ => (h2.corrScale (hr.r n) : ℂ)) := by
      have h := hcentralCorr.add htail
      refine h.congr_left ?_
      intro n
      ring
    have hratio := coeff_ratio_eq_scaled_saddleJ_eventually hf hr
    have htarget :
        (fun n : ℕ =>
          p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ)))
          =ᶠ[atTop]
        (fun n : ℕ =>
          (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
                saddleJt f hr.r (HAdmissible.Δ hf hr) n) -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ))) := by
      filter_upwards [hratio] with n hn
      rw [hn]
    exact htarget.trans_isLittleO hscaled

end
end

section
/-!
# Second-order saddle data for involutions

This file adds the second-order correction layer for
`exp (z + z^2 / 2)`.  The logarithmic saddle derivatives are
`b₃(r)=r+4r²` and `b₄(r)=r+8r²`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

namespace InvolutionHAdmissible

/-- The error after inserting the explicit involution correction `-1/(6n)`. -/
def involSecondOrderOneOverNError (n : ℕ) : ℂ :=
  involCoeffC n / involSecondOrderSaddleScale n -
    (1 - (1 : ℂ) / (6 * (n : ℂ)))

/-- The final involution second-order comparison scale. -/
def involOneOverNScale (n : ℕ) : ℂ :=
  ((1 : ℝ) / (n : ℝ) : ℂ)

lemma invol_saddleCorrection_eq {r : ℝ} (hr : r ≠ 0) :
    saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real r =
      -((16 * r ^ 2 + 5 * r + 1) / (12 * r * (1 + 2 * r) ^ 3)) := by
  unfold saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
  field_simp [hr]
  ring

private lemma complex_isLittleO_of_norm_div_tendsto_zero_nat
    (u : ℕ → ℂ) (c : ℕ → ℝ)
    (hcpos : ∀ᶠ n in atTop, 0 < c n)
    (h : Tendsto (fun n : ℕ => ‖u n‖ / c n) atTop (𝓝 0)) :
    u =o[atTop] (fun n : ℕ => (c n : ℂ)) := by
  rw [isLittleO_iff_tendsto']
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Tendsto.congr' ?_ h
    filter_upwards [hcpos] with n hcn
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcn]
  · filter_upwards [hcpos] with n hcn hzero
    exact (hcn.ne' (Complex.ofReal_eq_zero.mp hzero)).elim

lemma involSecondCorrScale_eq_rational {r : ℝ} (hr : 0 < r) :
    involSecondCorrScale r =
      (2 + 18 * r + 32 * r ^ 2) / (r * (1 + 2 * r) ^ 3) := by
  unfold involSecondCorrScale saddleCorrectionScale involSaddleBReal involSaddleB3Real
    involSaddleB4Real
  have h4 : 0 ≤ r + 8 * r ^ 2 := by positivity
  rw [abs_of_nonneg h4]
  field_simp [hr.ne']
  ring

lemma involSecondCorrScale_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < involSecondCorrScale r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  unfold involSecondCorrScale saddleCorrectionScale involSaddleBReal involSaddleB3Real
    involSaddleB4Real
  positivity

lemma involSecondCorrScale_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ involSecondCorrScale r :=
  involSecondCorrScale_pos_eventually.mono fun _ h => h.le

lemma involSecondCorrScale_le_rpow_eventually :
    ∀ᶠ r : ℝ in atTop, involSecondCorrScale r ≤ 100 * r ^ (-(2 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [involSecondCorrScale_eq_rational hrpos]
  rw [Real.rpow_neg hrpos.le]
  field_simp [hrpos.ne']
  have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
    exact (Real.rpow_natCast r 2).symm
  calc
    (2 + 18 * r + r ^ 2 * 32) * r ^ (2 : ℝ)
        = (2 + 18 * r + r ^ 2 * 32) * r ^ 2 := by rw [← hr2_rpow]
    _ = 2 * r ^ 2 + 18 * r ^ 3 + 32 * r ^ 4 := by ring
    _ ≤ 100 * r + 600 * r ^ 2 + 1200 * r ^ 3 + 800 * r ^ 4 := by
      have hdiff : 0 ≤ 100 * r + 598 * r ^ 2 + 1182 * r ^ 3 + 768 * r ^ 4 := by
        positivity
      nlinarith [hdiff]
    _ = r * (1 + 2 * r) ^ 3 * 100 := by ring

lemma involSecondCorrScale_lower_eventually :
    ∀ᶠ r : ℝ in atTop,
      (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) ≤ involSecondCorrScale r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [involSecondCorrScale_eq_rational hrpos]
  rw [Real.rpow_neg hrpos.le]
  field_simp [hrpos.ne']
  have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
    exact (Real.rpow_natCast r 2).symm
  calc
    16 * r * (1 + 2 * r) ^ 3
        ≤ 27 * r ^ 2 * (2 + 18 * r + r ^ 2 * 32) := by
          ring_nf
          nlinarith [hr, mul_nonneg hrpos.le hrpos.le, show 0 ≤ r ^ 3 by positivity,
            show 0 ≤ r ^ 4 by positivity]
    _ = 27 * r ^ (2 : ℝ) * (2 + 18 * r + r ^ 2 * 32) := by rw [← hr2_rpow]

lemma involSecondCorrScale_tendsto_zero :
    Tendsto involSecondCorrScale atTop (𝓝 0) := by
  have hupper : Tendsto (fun r : ℝ => 100 * r ^ (-(2 : ℝ))) atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul (100 : ℝ)
  exact squeeze_zero' involSecondCorrScale_nonneg_eventually
    involSecondCorrScale_le_rpow_eventually hupper

lemma involTailE_second_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r /
          involSecondCorrScale r)
      atTop (𝓝 0) := by
  have hupper :
      Tendsto
        (fun r : ℝ =>
          (Real.sqrt (6 * Real.pi) * r * involTailE r) /
            ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))))
        atTop (𝓝 0) := by
    let c : ℝ := 1 / (2 * Real.pi ^ 2)
    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hbase :
        Tendsto (fun y : ℝ => y ^ (12 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (12 : ℝ) c hc
    have hy : Tendsto (fun r : ℝ => r ^ (1 / 4 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    have hcomp :
        Tendsto
          (fun r : ℝ =>
            (r ^ (1 / 4 : ℝ)) ^ (12 : ℝ) * Real.exp (-c * r ^ (1 / 4 : ℝ)))
          atTop (𝓝 0) := hbase.comp hy
    have hscaled :
        Tendsto
          (fun r : ℝ =>
            (Real.sqrt (6 * Real.pi) * (27 / 16 : ℝ)) *
              ((r ^ (1 / 4 : ℝ)) ^ (12 : ℝ) *
                Real.exp (-c * r ^ (1 / 4 : ℝ))))
          atTop (𝓝 0) := by
      simpa using hcomp.const_mul (Real.sqrt (6 * Real.pi) * (27 / 16 : ℝ))
    refine Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hr0 : 0 ≤ r := hr.le
    have hrpow12 : (r ^ (1 / 4 : ℝ)) ^ (12 : ℝ) = r ^ 3 := by
      calc
        (r ^ (1 / 4 : ℝ)) ^ (12 : ℝ) = r ^ ((1 / 4 : ℝ) * 12) :=
          (Real.rpow_mul hr0 _ _).symm
        _ = r ^ (3 : ℝ) :=
          congrArg (fun e : ℝ => r ^ e) (by norm_num : (1 / 4 : ℝ) * 12 = 3)
        _ = r ^ (3 : ℕ) := Real.rpow_natCast r 3
    unfold involTailE
    dsimp [c]
    rw [hrpow12]
    rw [Real.rpow_neg hr0]
    field_simp [hr.ne']
    exact (Real.rpow_natCast r 2).symm
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_lower_eventually] with
      r hr hcl
    have hαpos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
      positivity
    have hcpos : 0 < involSecondCorrScale r := lt_of_lt_of_le hαpos hcl
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by unfold involTailE; positivity)) hcpos.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_lower_eventually] with
      r hr hcl
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hαpos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by positivity
    have hE_nonneg : 0 ≤ involTailE r := by
      unfold involTailE
      positivity
    have hB_le : involSaddleBReal r ≤ 3 * r ^ 2 := by
      unfold involSaddleBReal
      nlinarith [hr]
    have hsqrt :
        Real.sqrt (2 * Real.pi * involSaddleBReal r) ≤ Real.sqrt (6 * Real.pi) * r := by
      have hmul : 2 * Real.pi * involSaddleBReal r ≤ 6 * Real.pi * r ^ 2 := by
        calc
          2 * Real.pi * involSaddleBReal r
              ≤ 2 * Real.pi * (3 * r ^ 2) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 6 * Real.pi * r ^ 2 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * involSaddleBReal r)
            ≤ Real.sqrt (6 * Real.pi * r ^ 2) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (6 * Real.pi) * r := by
          have h6pi : 0 ≤ 6 * Real.pi := by positivity
          rw [Real.sqrt_mul h6pi (r ^ 2)]
          rw [Real.sqrt_sq hr0]
    have hnum :
        Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r ≤
          Real.sqrt (6 * Real.pi) * r * involTailE r := by
      calc
        Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r
            ≤ (Real.sqrt (6 * Real.pi) * r) * involTailE r :=
              mul_le_mul_of_nonneg_right hsqrt hE_nonneg
        _ = Real.sqrt (6 * Real.pi) * r * involTailE r := by ring
    calc
      Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r /
          involSecondCorrScale r
          ≤ Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r /
              ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) :=
            div_le_div_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) hE_nonneg) hαpos hcl
      _ ≤ (Real.sqrt (6 * Real.pi) * r * involTailE r) /
              ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) :=
            div_le_div_of_nonneg_right hnum hαpos.le

lemma invol_tail_second_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in atTop, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * involSaddleBReal r) * E r /
          involSecondCorrScale r)
        atTop (𝓝 0) ∧
      (∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        involSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt involFun r n θ‖ ≤ E r) := by
  exact ⟨involTailE, involTailE_nonneg_eventually, involTailE_second_decay,
    invol_tail_bound_eventually⟩

private def expLocalRemainderFifth (θ : ℝ) : ℂ :=
  ExpStirling.expLocalRemainder θ -
    ((((θ : ℂ) * Complex.I) ^ 3) / (((3 : ℕ).factorial : ℕ) : ℂ) +
      (((θ : ℂ) * Complex.I) ^ 4) / (((4 : ℕ).factorial : ℕ) : ℂ))

private lemma expLocalRemainderFifth_norm_le {θ : ℝ} (hθ : |θ| ≤ 2) :
    ‖expLocalRemainderFifth θ‖ ≤ Real.exp 2 * |θ| ^ 5 := by
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
      Real.exp 2 * |θ| ^ 5
  rw [hleft]
  calc
    ‖Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ)‖
        ≤ ‖u‖ ^ 5 * Real.exp ‖u‖ := htail
    _ = |θ| ^ 5 * Real.exp |θ| := by rw [hnorm]
    _ ≤ |θ| ^ 5 * Real.exp 2 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 5)
    _ = Real.exp 2 * |θ| ^ 5 := by ring

private lemma involLocalExponent_split_fifth (r θ : ℝ) :
    involLocalExponent r θ =
      -Complex.I * ((involSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
        ((involSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4 +
        (r : ℂ) * expLocalRemainderFifth θ +
        (((r ^ 2 / 2 : ℝ) : ℂ) * expLocalRemainderFifth (2 * θ)) := by
  unfold involLocalExponent expLocalRemainderFifth involSaddleB3Real involSaddleB4Real
  ring_nf
  simp [Complex.I_pow_three, Complex.I_pow_four]
  ring_nf

private def involScaledCubic (r x : ℝ) : ℂ :=
  -Complex.I *
    ((involSaddleB3Real r : ℂ) /
      (6 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3)) * (x : ℂ) ^ 3

private def involScaledQuartic (r x : ℝ) : ℂ :=
  ((involSaddleB4Real r : ℂ) / (24 * (involSaddleBReal r : ℂ) ^ 2)) *
    (x : ℂ) ^ 4

private def involScaledRemainder (r x : ℝ) : ℂ :=
  (r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (involSaddleBReal r)) +
    (((r ^ 2 / 2 : ℝ) : ℂ) *
      expLocalRemainderFifth (2 * (x / Real.sqrt (involSaddleBReal r))))

private lemma involLocalExponent_scaled_split {r x : ℝ}
    (hb : 0 < involSaddleBReal r) :
    involLocalExponent r (x / Real.sqrt (involSaddleBReal r)) =
      involScaledCubic r x + involScaledQuartic r x + involScaledRemainder r x := by
  have hsqrt_ne : (Real.sqrt (involSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  rw [involLocalExponent_split_fifth]
  unfold involScaledCubic involScaledQuartic involScaledRemainder
  have hsqrt_sq :
      ((Real.sqrt (involSaddleBReal r) : ℂ) ^ 2) =
        (involSaddleBReal r : ℂ) := by
    exact_mod_cast (Real.sq_sqrt hb.le)
  have hsqrt_inv_pow4 :
      ((Real.sqrt (r + r ^ 2 * 2) : ℂ)⁻¹) ^ 4 =
        (↑r ^ 2 + ↑r ^ 3 * 4 + ↑r ^ 4 * 4 : ℂ)⁻¹ := by
    rw [inv_pow]
    congr 1
    have harg : r + r ^ 2 * 2 = involSaddleBReal r := by
      unfold involSaddleBReal
      ring
    calc
      (Real.sqrt (r + r ^ 2 * 2) : ℂ) ^ 4 =
          ((Real.sqrt (involSaddleBReal r) : ℂ) ^ 2) ^ 2 := by
            rw [harg]
            ring
      _ = (involSaddleBReal r : ℂ) ^ 2 := by rw [hsqrt_sq]
      _ = (↑r ^ 2 + ↑r ^ 3 * 4 + ↑r ^ 4 * 4 : ℂ) := by
        unfold involSaddleBReal
        exact_mod_cast (by ring : (r + 2 * r ^ 2) ^ 2 = r ^ 2 + r ^ 3 * 4 + r ^ 4 * 4)
  simp [Complex.ofReal_inv, div_eq_mul_inv]
  ring_nf
  rw [hsqrt_inv_pow4]
  ring

private lemma saddleSecondPoly_eq_scaled_terms {r x : ℝ}
    (hb : 0 < involSaddleBReal r) :
    saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x =
      1 + involScaledCubic r x + involScaledQuartic r x +
        (involScaledCubic r x) ^ 2 / 2 := by
  have hsqrt_sq :
      ((Real.sqrt (involSaddleBReal r) : ℂ) ^ 2) =
        (involSaddleBReal r : ℂ) := by
    exact_mod_cast (Real.sq_sqrt hb.le)
  have hsqrt_ne : (Real.sqrt (involSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (involSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_pow6 :
      (Real.sqrt (involSaddleBReal r) : ℂ) ^ 6 =
        (involSaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (involSaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (involSaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (involSaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
  unfold saddleSecondPoly involScaledCubic involScaledQuartic
  field_simp [hsqrt_ne, hb_ne]
  ring_nf
  rw [hsqrt_pow6, Complex.I_sq]
  norm_num [Complex.ofReal_pow]
  ring

private def involGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10)

private lemma involGaussianDom_nonneg (x : ℝ) : 0 ≤ involGaussianDom x := by
  unfold involGaussianDom
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

private lemma involGaussianDom_integrable : Integrable involGaussianDom := by
  unfold involGaussianDom
  have hsum :
      Integrable
        ((((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 5) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 7)) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 8)) +
          ((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 9) +
            (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 10))) :=
    (((gaussian_abs_monomial_integrable 5).add
      (gaussian_abs_monomial_integrable 7)).add
      (gaussian_abs_monomial_integrable 8)).add
      (((gaussian_abs_monomial_integrable 9).add
        (gaussian_abs_monomial_integrable 10)))
  convert hsum using 1
  ext x
  simp only [Pi.add_apply]
  ring_nf

private lemma involGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, involGaussianDom x := by
  exact integral_nonneg (fun x => involGaussianDom_nonneg x)

private lemma involSaddleBReal_pos_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 < involSaddleBReal r := by
  unfold involSaddleBReal
  nlinarith [hr, sq_nonneg r]

private lemma invol_sqrtB_ge_r {r : ℝ} (hr : 1 ≤ r) :
    r ≤ Real.sqrt (involSaddleBReal r) := by
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := by
    unfold involSaddleBReal
    nlinarith [sq_nonneg r]
  exact Real.le_sqrt_of_sq_le hb_ge

private lemma invol_sqrtB_le_two_r {r : ℝ} (hr : 1 ≤ r) :
    Real.sqrt (involSaddleBReal r) ≤ 2 * r := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hmul : involSaddleBReal r ≤ (2 * r) ^ 2 := by
    unfold involSaddleBReal
    nlinarith [hr, sq_nonneg r]
  calc
    Real.sqrt (involSaddleBReal r) ≤ Real.sqrt ((2 * r) ^ 2) :=
      Real.sqrt_le_sqrt hmul
    _ = 2 * r := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hr0)]

private lemma involScaledCubic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖involScaledCubic r x‖ ≤ 10 * |x| ^ 3 / r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r hr
  have hsqrt3_ge : r ^ 3 ≤ (Real.sqrt (involSaddleBReal r)) ^ 3 :=
    pow_le_pow_left₀ hrpos.le hsqrt_ge 3
  have hb3_nonneg : 0 ≤ involSaddleB3Real r := by
    unfold involSaddleB3Real
    nlinarith [hr, sq_nonneg r]
  have hb3_le : involSaddleB3Real r ≤ 5 * r ^ 2 := by
    unfold involSaddleB3Real
    nlinarith [hr]
  have hcoef :
      ‖(involSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3)‖ ≤ 1 / r := by
    have hdenpos : 0 < 6 * (Real.sqrt (involSaddleBReal r)) ^ 3 := by positivity
    calc
      ‖(involSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3)‖
          = involSaddleB3Real r /
              (6 * |Real.sqrt (involSaddleBReal r)| ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb3_nonneg]
            simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ = involSaddleB3Real r /
              (6 * (Real.sqrt (involSaddleBReal r)) ^ 3) := by
            rw [abs_of_pos hsqrt_pos]
      _ ≤ (5 * r ^ 2) / (6 * r ^ 3) := by
        exact div_le_div₀ (by positivity) hb3_le (by positivity) (by nlinarith [hsqrt3_ge])
      _ ≤ 1 / r := by
        field_simp [hrpos.ne']
        nlinarith
  calc
    ‖involScaledCubic r x‖
        = ‖(involSaddleB3Real r : ℂ) /
            (6 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3)‖ * |x| ^ 3 := by
          unfold involScaledCubic
          rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r) * |x| ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 3)
    _ ≤ 10 * |x| ^ 3 / r := by
      field_simp [hrpos.ne']
      nlinarith [pow_nonneg (abs_nonneg x) 3]

private lemma involScaledQuartic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖involScaledQuartic r x‖ ≤ 10 * |x| ^ 4 / r ^ 2 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := by
    unfold involSaddleBReal
    nlinarith [sq_nonneg r]
  have hb4_nonneg : 0 ≤ involSaddleB4Real r := by
    unfold involSaddleB4Real
    nlinarith [hr, sq_nonneg r]
  have hb4_le : involSaddleB4Real r ≤ 9 * r ^ 2 := by
    unfold involSaddleB4Real
    nlinarith [hr]
  have hb_sq_ge : r ^ 4 ≤ (involSaddleBReal r) ^ 2 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ ≤ (involSaddleBReal r) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg r) hb_ge 2
  have hcoef :
      ‖(involSaddleB4Real r : ℂ) / (24 * (involSaddleBReal r : ℂ) ^ 2)‖ ≤
        1 / r ^ 2 := by
    calc
      ‖(involSaddleB4Real r : ℂ) / (24 * (involSaddleBReal r : ℂ) ^ 2)‖
          = involSaddleB4Real r / (24 * ‖(involSaddleBReal r : ℂ)‖ ^ 2) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb4_nonneg]
            simp [norm_pow]
      _ = involSaddleB4Real r / (24 * (involSaddleBReal r) ^ 2) := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]
      _ ≤ (9 * r ^ 2) / (24 * r ^ 4) := by
        exact div_le_div₀ (by positivity) hb4_le (by positivity) (by nlinarith [hb_sq_ge])
      _ ≤ 1 / r ^ 2 := by
        have hr2pos : 0 < r ^ 2 := sq_pos_of_pos hrpos
        field_simp [hrpos.ne', hr2pos.ne']
        nlinarith
  calc
    ‖involScaledQuartic r x‖
        = ‖(involSaddleB4Real r : ℂ) /
            (24 * (involSaddleBReal r : ℂ) ^ 2)‖ * |x| ^ 4 := by
          unfold involScaledQuartic
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 2) * |x| ^ 4 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 4)
    _ ≤ 10 * |x| ^ 4 / r ^ 2 := by
      have hr2pos : 0 < r ^ 2 := sq_pos_of_pos hrpos
      field_simp [hr2pos.ne']
      nlinarith [pow_nonneg (abs_nonneg x) 4]

private lemma involScaledRemainder_norm_le {r x : ℝ}
    (hr : 1 ≤ r) (hθ : |x / Real.sqrt (involSaddleBReal r)| ≤ 1) :
    ‖involScaledRemainder r x‖ ≤ 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r hr
  have hθ_two : |2 * (x / Real.sqrt (involSaddleBReal r))| ≤ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hθ_abs_le : |x / Real.sqrt (involSaddleBReal r)| ≤ |x| / r := by
    rw [abs_div, abs_of_pos hsqrt_pos]
    exact div_le_div_of_nonneg_left (abs_nonneg x) hrpos hsqrt_ge
  have hθ5_le : |x / Real.sqrt (involSaddleBReal r)| ^ 5 ≤ (|x| / r) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hθ_abs_le 5
  have hrem1 := expLocalRemainderFifth_norm_le (by linarith : |x / Real.sqrt (involSaddleBReal r)| ≤ 2)
  have hrem2 := expLocalRemainderFifth_norm_le hθ_two
  have hmain :
      ‖involScaledRemainder r x‖ ≤
        r * (Real.exp 2 * (|x| / r) ^ 5) +
          (r ^ 2 / 2) * (Real.exp 2 * (2 * (|x| / r)) ^ 5) := by
    unfold involScaledRemainder
    calc
      ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (involSaddleBReal r)) +
          (((r ^ 2 / 2 : ℝ) : ℂ) *
            expLocalRemainderFifth (2 * (x / Real.sqrt (involSaddleBReal r))))‖
          ≤ ‖(r : ℂ) * expLocalRemainderFifth (x / Real.sqrt (involSaddleBReal r))‖ +
              ‖(((r ^ 2 / 2 : ℝ) : ℂ) *
                expLocalRemainderFifth (2 * (x / Real.sqrt (involSaddleBReal r))))‖ :=
            norm_add_le _ _
      _ ≤ r * (Real.exp 2 * (|x| / r) ^ 5) +
            (r ^ 2 / 2) * (Real.exp 2 * |2 * (x / Real.sqrt (involSaddleBReal r))| ^ 5) := by
          gcongr
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
            exact mul_le_mul_of_nonneg_left
              (hrem1.trans (mul_le_mul_of_nonneg_left hθ5_le (Real.exp_pos 2).le))
              hrpos.le
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hcoef : 0 ≤ r ^ 2 / 2 := by positivity
            rw [abs_of_nonneg hcoef]
            exact mul_le_mul_of_nonneg_left hrem2 hcoef
      _ ≤ r * (Real.exp 2 * (|x| / r) ^ 5) +
            (r ^ 2 / 2) * (Real.exp 2 * (2 * (|x| / r)) ^ 5) := by
          gcongr
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact mul_le_mul_of_nonneg_left hθ_abs_le (by norm_num)
  calc
    ‖involScaledRemainder r x‖
        ≤ r * (Real.exp 2 * (|x| / r) ^ 5) +
          (r ^ 2 / 2) * (Real.exp 2 * (2 * (|x| / r)) ^ 5) := hmain
    _ ≤ 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
      field_simp [hrpos.ne']
      ring_nf
      nlinarith [Real.exp_pos 2, pow_nonneg (abs_nonneg x) 5]

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

private def involLocalL1Const : ℝ :=
  100 * Real.exp 2 + Real.exp 1 * (1000 * Real.exp 2) ^ 3 +
    (200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2)

private lemma involLocalL1Const_pos : 0 < involLocalL1Const := by
  unfold involLocalL1Const
  positivity

private lemma invol_local_integrand_bound {r x : ℝ}
    (hr : 1 ≤ r)
    (hθ : |x / Real.sqrt (involSaddleBReal r)| ≤ 1)
    (hx2r : |x| ≤ 2 * r)
    (hWnorm : ‖involLocalExponent r (x / Real.sqrt (involSaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
      ≤ involLocalL1Const * involGaussianDom x / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
  let C : ℂ := involScaledCubic r x
  let Q : ℂ := involScaledQuartic r x
  let R : ℂ := involScaledRemainder r x
  let W : ℂ := involLocalExponent r (x / Real.sqrt (involSaddleBReal r))
  have hWsplit : W = C + Q + R := by
    dsimp [W, C, Q, R]
    exact involLocalExponent_scaled_split hbpos
  have hP :
      saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x =
        1 + C + Q + C ^ 2 / 2 := by
    dsimp [C, Q]
    exact saddleSecondPoly_eq_scaled_terms hbpos
  have herr := complex_exp_second_error_bound C Q R W hWsplit (by simpa [W] using hWnorm)
  have hC : ‖C‖ ≤ 10 * |x| ^ 3 / r := by
    dsimp [C]
    exact involScaledCubic_norm_le hr
  have hQ : ‖Q‖ ≤ 10 * |x| ^ 4 / r ^ 2 := by
    dsimp [Q]
    exact involScaledQuartic_norm_le hr
  have hR : ‖R‖ ≤ 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
    dsimp [R]
    exact involScaledRemainder_norm_le hr hθ
  have hy_nonneg : 0 ≤ |x| := abs_nonneg x
  have hr2pos : 0 < r ^ 2 := sq_pos_of_pos hrpos
  have hr3pos : 0 < r ^ 3 := by positivity
  have hy2_le : |x| ^ 2 ≤ (2 * r) ^ 2 :=
    (sq_le_sq₀ hy_nonneg (mul_nonneg (by norm_num) hrpos.le)).mpr hx2r
  have hQ_cubic : 10 * |x| ^ 4 / r ^ 2 ≤ 20 * |x| ^ 3 / r := by
    have hmul : 10 * |x| ^ 3 * |x| ≤ 10 * |x| ^ 3 * (2 * r) :=
      mul_le_mul_of_nonneg_left hx2r (by positivity)
    field_simp [hrpos.ne', hr2pos.ne']
    nlinarith [hmul]
  have hR_cubic :
      100 * Real.exp 2 * |x| ^ 5 / r ^ 3 ≤
        400 * Real.exp 2 * |x| ^ 3 / r := by
    field_simp [hrpos.ne', hr2pos.ne', hr3pos.ne']
    nlinarith [hy2_le, Real.exp_pos 2, pow_nonneg hy_nonneg 3]
  have hexp2_ge_one : 1 ≤ Real.exp 2 := by
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2)
  have hWpoly : ‖W‖ ≤ 1000 * Real.exp 2 * |x| ^ 3 / r := by
    calc
      ‖W‖ = ‖C + Q + R‖ := by rw [hWsplit]
      _ ≤ ‖C‖ + ‖Q‖ + ‖R‖ := by
        calc
          ‖C + Q + R‖ ≤ ‖C + Q‖ + ‖R‖ := norm_add_le _ _
          _ ≤ (‖C‖ + ‖Q‖) + ‖R‖ := add_le_add (norm_add_le _ _) (le_refl _)
          _ = ‖C‖ + ‖Q‖ + ‖R‖ := by ring
      _ ≤ 10 * |x| ^ 3 / r + 10 * |x| ^ 4 / r ^ 2 +
            100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
        exact add_le_add (add_le_add hC hQ) hR
      _ ≤ 10 * |x| ^ 3 / r + 20 * |x| ^ 3 / r +
            400 * Real.exp 2 * |x| ^ 3 / r := by
        exact add_le_add (add_le_add (le_refl _) hQ_cubic) hR_cubic
      _ ≤ 1000 * Real.exp 2 * |x| ^ 3 / r := by
        field_simp [hrpos.ne']
        nlinarith [hexp2_ge_one, pow_nonneg hy_nonneg 3]
  have hWcube :
      Real.exp 1 * ‖W‖ ^ 3 ≤
        Real.exp 1 * (1000 * Real.exp 2) ^ 3 * |x| ^ 9 / r ^ 3 := by
    have hpow := pow_le_pow_left₀ (norm_nonneg W) hWpoly 3
    calc
      Real.exp 1 * ‖W‖ ^ 3
          ≤ Real.exp 1 * (1000 * Real.exp 2 * |x| ^ 3 / r) ^ 3 :=
            mul_le_mul_of_nonneg_left hpow (Real.exp_pos 1).le
      _ = Real.exp 1 * (1000 * Real.exp 2) ^ 3 * |x| ^ 9 / r ^ 3 := by
        field_simp [hrpos.ne']
  have hprod_bound :
      (10 * |x| ^ 4 / r ^ 2 + 100 * Real.exp 2 * |x| ^ 5 / r ^ 3) *
          (2 * (10 * |x| ^ 3 / r) + 10 * |x| ^ 4 / r ^ 2 +
            100 * Real.exp 2 * |x| ^ 5 / r ^ 3)
        ≤ (200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) *
            (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
    let D : ℝ := 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hr_le_sq : r ≤ r ^ 2 := by nlinarith [hr, sq_nonneg r]
    have hr_sq_le_cu : r ^ 2 ≤ r ^ 3 := by
      nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]
    have hr3_le_r4 : r ^ 3 ≤ r ^ 4 := by
      nlinarith [hr, hr_le_sq, hr_sq_le_cu, show 0 ≤ r ^ 4 by positivity]
    have hr3_le_r5 : r ^ 3 ≤ r ^ 5 := by
      nlinarith [hr, hr_le_sq, hr_sq_le_cu, hr3_le_r4, show 0 ≤ r ^ 5 by positivity]
    have hr3_le_r6 : r ^ 3 ≤ r ^ 6 := by
      nlinarith [hr, hr_le_sq, hr_sq_le_cu, hr3_le_r4, hr3_le_r5,
        show 0 ≤ r ^ 6 by positivity]
    have hD200 : 200 ≤ D := by
      have hnon : 0 ≤ 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by positivity
      dsimp [D]
      calc
        (200 : ℝ) ≤ 200 + (3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) :=
          le_add_of_nonneg_right hnon
        _ = 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by ring
    have hD8 : 100 + 2000 * Real.exp 2 ≤ D := by
      have hnon : 0 ≤ 100 + 1000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by
        positivity
      dsimp [D]
      calc
        100 + 2000 * Real.exp 2
            ≤ 100 + 2000 * Real.exp 2 +
                (100 + 1000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) :=
          le_add_of_nonneg_right hnon
        _ = 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by ring
    have hD9 : 2000 * Real.exp 2 ≤ D := by
      have hnon : 0 ≤ 200 + 1000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by
        positivity
      dsimp [D]
      calc
        2000 * Real.exp 2
            ≤ 2000 * Real.exp 2 +
                (200 + 1000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) :=
          le_add_of_nonneg_right hnon
        _ = 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by ring
    have hD10 : 10000 * (Real.exp 2) ^ 2 ≤ D := by
      have hnon : 0 ≤ 200 + 3000 * Real.exp 2 := by positivity
      dsimp [D]
      calc
        10000 * (Real.exp 2) ^ 2
            ≤ 10000 * (Real.exp 2) ^ 2 + (200 + 3000 * Real.exp 2) :=
          le_add_of_nonneg_right hnon
        _ = 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2 := by ring
    have hexpand :
        (10 * |x| ^ 4 / r ^ 2 + 100 * Real.exp 2 * |x| ^ 5 / r ^ 3) *
            (2 * (10 * |x| ^ 3 / r) + 10 * |x| ^ 4 / r ^ 2 +
              100 * Real.exp 2 * |x| ^ 5 / r ^ 3) =
          200 * |x| ^ 7 / r ^ 3 +
            (100 + 2000 * Real.exp 2) * |x| ^ 8 / r ^ 4 +
            2000 * Real.exp 2 * |x| ^ 9 / r ^ 5 +
            10000 * (Real.exp 2) ^ 2 * |x| ^ 10 / r ^ 6 := by
      field_simp [hrpos.ne']
      ring
    rw [hexpand]
    have h7 : 200 * |x| ^ 7 / r ^ 3 ≤ D * |x| ^ 7 / r ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hD200 (pow_nonneg hy_nonneg 7)) hr3pos.le
    have h8 : (100 + 2000 * Real.exp 2) * |x| ^ 8 / r ^ 4 ≤
        D * |x| ^ 8 / r ^ 3 := by
      calc
        (100 + 2000 * Real.exp 2) * |x| ^ 8 / r ^ 4
            ≤ D * |x| ^ 8 / r ^ 4 :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hD8 (pow_nonneg hy_nonneg 8))
                (by positivity)
        _ ≤ D * |x| ^ 8 / r ^ 3 :=
              div_le_div_of_nonneg_left
                (mul_nonneg hD (pow_nonneg hy_nonneg 8)) hr3pos hr3_le_r4
    have h9 : 2000 * Real.exp 2 * |x| ^ 9 / r ^ 5 ≤
        D * |x| ^ 9 / r ^ 3 := by
      calc
        2000 * Real.exp 2 * |x| ^ 9 / r ^ 5
            ≤ D * |x| ^ 9 / r ^ 5 :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hD9 (pow_nonneg hy_nonneg 9))
                (by positivity)
        _ ≤ D * |x| ^ 9 / r ^ 3 :=
              div_le_div_of_nonneg_left
                (mul_nonneg hD (pow_nonneg hy_nonneg 9)) hr3pos hr3_le_r5
    have h10 : 10000 * (Real.exp 2) ^ 2 * |x| ^ 10 / r ^ 6 ≤
        D * |x| ^ 10 / r ^ 3 := by
      calc
        10000 * (Real.exp 2) ^ 2 * |x| ^ 10 / r ^ 6
            ≤ D * |x| ^ 10 / r ^ 6 :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hD10 (pow_nonneg hy_nonneg 10))
                (by positivity)
        _ ≤ D * |x| ^ 10 / r ^ 3 :=
              div_le_div_of_nonneg_left
                (mul_nonneg hD (pow_nonneg hy_nonneg 10)) hr3pos hr3_le_r6
    calc
      200 * |x| ^ 7 / r ^ 3 +
            (100 + 2000 * Real.exp 2) * |x| ^ 8 / r ^ 4 +
            2000 * Real.exp 2 * |x| ^ 9 / r ^ 5 +
            10000 * (Real.exp 2) ^ 2 * |x| ^ 10 / r ^ 6
          ≤ D * |x| ^ 7 / r ^ 3 + D * |x| ^ 8 / r ^ 3 +
              D * |x| ^ 9 / r ^ 3 + D * |x| ^ 10 / r ^ 3 := by
            exact add_le_add (add_le_add (add_le_add h7 h8) h9) h10
      _ = D * (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
        ring
  have hquad :
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖)
        ≤ (200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) *
            (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
    have hQR :
        ‖Q‖ + ‖R‖ ≤
          10 * |x| ^ 4 / r ^ 2 + 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 :=
      add_le_add hQ hR
    have hCQR :
        2 * ‖C‖ + ‖Q‖ + ‖R‖ ≤
          2 * (10 * |x| ^ 3 / r) + 10 * |x| ^ 4 / r ^ 2 +
            100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)) hQ) hR
    have hQR_nonneg :
        0 ≤ 10 * |x| ^ 4 / r ^ 2 + 100 * Real.exp 2 * |x| ^ 5 / r ^ 3 := by
      positivity
    exact (mul_le_mul hQR hCQR (by positivity) hQR_nonneg).trans hprod_bound
  have hdiff :
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
        involLocalL1Const *
          (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
    calc
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
          ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
              (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := herr
      _ ≤ Real.exp 1 * (1000 * Real.exp 2) ^ 3 * |x| ^ 9 / r ^ 3 +
            100 * Real.exp 2 * |x| ^ 5 / r ^ 3 +
            (200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2) *
              (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
        exact add_le_add (add_le_add hWcube hR) hquad
      _ ≤ involLocalL1Const *
            (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3 := by
        let A : ℝ := 100 * Real.exp 2
        let B : ℝ := Real.exp 1 * (1000 * Real.exp 2) ^ 3
        let D : ℝ := 200 + 3000 * Real.exp 2 + 10000 * (Real.exp 2) ^ 2
        let S : ℝ := |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10
        let T : ℝ := |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10
        have hA : 0 ≤ A := by dsimp [A]; positivity
        have hB : 0 ≤ B := by dsimp [B]; positivity
        have hD : 0 ≤ D := by dsimp [D]; positivity
        have hy5S : |x| ^ 5 ≤ S := by
          dsimp [S]
          have hrest : 0 ≤ |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 := by
            exact add_nonneg (add_nonneg (add_nonneg
              (pow_nonneg hy_nonneg 7) (pow_nonneg hy_nonneg 8))
              (pow_nonneg hy_nonneg 9)) (pow_nonneg hy_nonneg 10)
          calc
            |x| ^ 5 ≤ |x| ^ 5 + (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) :=
              le_add_of_nonneg_right hrest
            _ = |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 := by ring
        have hy9S : |x| ^ 9 ≤ S := by
          dsimp [S]
          have hrest : 0 ≤ |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 10 := by
            exact add_nonneg (add_nonneg (add_nonneg
              (pow_nonneg hy_nonneg 5) (pow_nonneg hy_nonneg 7))
              (pow_nonneg hy_nonneg 8)) (pow_nonneg hy_nonneg 10)
          calc
            |x| ^ 9 ≤ (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 10) + |x| ^ 9 :=
              le_add_of_nonneg_left hrest
            _ = |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 := by ring
        have hTS : T ≤ S := by
          dsimp [T, S]
          have h5 : 0 ≤ |x| ^ 5 := pow_nonneg hy_nonneg 5
          calc
            |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10
                ≤ |x| ^ 5 + (|x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) :=
                  le_add_of_nonneg_left h5
            _ = |x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 := by abel
        change B * |x| ^ 9 / r ^ 3 + A * |x| ^ 5 / r ^ 3 + D * T / r ^ 3 ≤
          (A + B + D) * S / r ^ 3
        have hnum :
            B * |x| ^ 9 + A * |x| ^ 5 + D * T ≤ (A + B + D) * S := by
          calc
            B * |x| ^ 9 + A * |x| ^ 5 + D * T
                ≤ B * S + A * S + D * S := by
                  exact add_le_add (add_le_add
                    (mul_le_mul_of_nonneg_left hy9S hB)
                    (mul_le_mul_of_nonneg_left hy5S hA))
                    (mul_le_mul_of_nonneg_left hTS hD)
            _ = (A + B + D) * S := by ring
        calc
          B * |x| ^ 9 / r ^ 3 + A * |x| ^ 5 / r ^ 3 + D * T / r ^ 3
              = (B * |x| ^ 9 + A * |x| ^ 5 + D * T) / r ^ 3 := by ring
          _ ≤ ((A + B + D) * S) / r ^ 3 :=
            div_le_div_of_nonneg_right hnum hr3pos.le
          _ = (A + B + D) * S / r ^ 3 := by rfl
  rw [invol_saddleLocalRatio_eq]
  rw [hP]
  change
    ‖Complex.exp (-(x ^ 2) / 2) *
        (Complex.exp W - (1 + C + Q + C ^ 2 / 2))‖ ≤
      involLocalL1Const * involGaussianDom x / r ^ 3
  rw [norm_mul]
  have hgauss :
      ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  rw [hgauss]
  unfold involGaussianDom
  calc
    Real.exp (-(x ^ 2) / 2) * ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
        ≤ Real.exp (-(x ^ 2) / 2) *
          (involLocalL1Const *
            (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10) / r ^ 3) :=
        mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ = involLocalL1Const *
          (Real.exp (-(x ^ 2) / 2) *
            (|x| ^ 5 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10)) / r ^ 3 := by
      ring

private lemma invol_local_integrand_continuous (r : ℝ) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ := by
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (involLocalExponent r (x / Real.sqrt (involSaddleBReal r))) -
            saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ := by
    unfold involLocalExponent ExpStirling.expLocalRemainder saddleSecondPoly
    fun_prop
  simpa [invol_saddleLocalRatio_eq] using h

private lemma involGaussianDom_continuous : Continuous involGaussianDom := by
  unfold involGaussianDom
  fun_prop

private lemma involGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, involGaussianDom x) ≤ ∫ x : ℝ, involGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral involGaussianDom_integrable
    (Eventually.of_forall involGaussianDom_nonneg)

theorem invol_local_second_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
          involSecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, involGaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact involGaussianDom_integral_nonneg
  have hupper_tendsto :
      Tendsto (fun r : ℝ => (involLocalL1Const * M * (27 / 16 : ℝ)) / r)
        atTop (𝓝 0) := by
    have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv, mul_assoc] using
      hinv.const_mul (involLocalL1Const * M * (27 / 16 : ℝ))
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, involSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), invol_delta_le_one_eventually,
      invol_local_exponent_norm_le_eventually,
      involLocalBound_tendsto_zero.eventually_le_const zero_lt_one,
      involSecondCorrScale_lower_eventually, involSecondCorrScale_pos_eventually] with
      r hr hδle hloc hsmall hcorrLower hcorrPos
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
    let G : ℝ → ℝ := fun x => (involLocalL1Const / r ^ 3) * involGaussianDom x
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one hr
    have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
    have hδnonneg : 0 ≤ involSaddleDeltaReal r := by
      unfold involSaddleDeltaReal
      positivity
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ G x := by
      intro x hx
      have hxabs : |x| ≤ L := by
        exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hθδ : |x / Real.sqrt (involSaddleBReal r)| ≤ involSaddleDeltaReal r := by
        rw [abs_div, abs_of_pos hsqrt_pos]
        calc
          |x| / Real.sqrt (involSaddleBReal r) ≤
              L / Real.sqrt (involSaddleBReal r) :=
            div_le_div_of_nonneg_right hxabs hsqrt_pos.le
          _ = involSaddleDeltaReal r := by
            dsimp [L]
            field_simp [hsqrt_pos.ne']
      have hθone : |x / Real.sqrt (involSaddleBReal r)| ≤ 1 := hθδ.trans hδle
      have hx2r : |x| ≤ 2 * r := by
        calc
          |x| ≤ L := hxabs
          _ ≤ Real.sqrt (involSaddleBReal r) := by
            dsimp [L]
            simpa [one_mul] using
              mul_le_mul_of_nonneg_right hδle (Real.sqrt_nonneg _)
          _ ≤ 2 * r := invol_sqrtB_le_two_r hr
      have hWnorm :
          ‖involLocalExponent r (x / Real.sqrt (involSaddleBReal r))‖ ≤ 1 :=
        (hloc (x / Real.sqrt (involSaddleBReal r)) hθδ).trans hsmall
      have hb := invol_local_integrand_bound hr hθone hx2r hWnorm
      dsimp [F, G]
      calc
        ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
            ≤ involLocalL1Const * involGaussianDom x / r ^ 3 := hb
        _ = involLocalL1Const / r ^ 3 * involGaussianDom x := by ring
    have hFint : IntervalIntegrable F volume (-L) L := by
      exact (invol_local_integrand_continuous r).intervalIntegrable _ _
    have hGint : IntervalIntegrable G volume (-L) L := by
      exact (involGaussianDom_continuous.const_mul (involLocalL1Const / r ^ 3)).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤ (involLocalL1Const / r ^ 3) * M := by
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, G x :=
          intervalIntegral.integral_mono_on hle hFint hGint hpoint
        _ = (involLocalL1Const / r ^ 3) * (∫ x in -L..L, involGaussianDom x) := by
          dsimp [G]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (involLocalL1Const / r ^ 3) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact involGaussianDom_window_le_integral hLnonneg)
            (div_nonneg involLocalL1Const_pos.le (by positivity))
    have hnum_nonneg : 0 ≤ (involLocalL1Const / r ^ 3) * M :=
      mul_nonneg (div_nonneg involLocalL1Const_pos.le (by positivity)) hM_nonneg
    have hscale_pos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by
      positivity
    have hmain :
        (∫ x in -L..L, F x) / involSecondCorrScale r ≤
          ((involLocalL1Const / r ^ 3) * M) /
            ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) := by
      calc
        (∫ x in -L..L, F x) / involSecondCorrScale r
            ≤ ((involLocalL1Const / r ^ 3) * M) / involSecondCorrScale r :=
              div_le_div_of_nonneg_right hIntBound hcorrPos.le
        _ ≤ ((involLocalL1Const / r ^ 3) * M) /
              ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) :=
            div_le_div_of_nonneg_left hnum_nonneg hscale_pos hcorrLower
    calc
      ((∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
          involSecondCorrScale r)
          = (∫ x in -L..L, F x) / involSecondCorrScale r := by rfl
      _ ≤ ((involLocalL1Const / r ^ 3) * M) /
            ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) := hmain
      _ = (involLocalL1Const * M * (27 / 16 : ℝ)) / r := by
        rw [Real.rpow_neg hrpos.le]
        field_simp [hrpos.ne']
        ring_nf
        norm_num

def involSecondOrderHAdmissibleCandidate : SecondOrderHAdmissible involHAdmissible where
  b3 := involSaddleB3Real
  b4 := involSaddleB4Real
  corrScale := involSecondCorrScale
  corrScale_pos := by
    simpa [involHAdmissible] using involSecondCorrScale_pos_eventually
  corrScale_tendsto_zero := by
    simpa [involHAdmissible] using involSecondCorrScale_tendsto_zero
  corrScale_dominates_correction := by
    refine ⟨1, by norm_num, ?_⟩
    exact Eventually.of_forall fun r => by
      simp [involHAdmissible, involSecondCorrScale]
  local_second_L1 := by
    simpa [involHAdmissible] using invol_local_second_L1
  tail_second_uniform := by
    simpa [involHAdmissible] using invol_tail_second_uniform

lemma involSecondCorrScale_saddleRadius_isBigO_one_over_n :
    (fun n : ℕ => (involSecondCorrScale (involSaddleRadius n) : ℂ))
      =O[atTop] involOneOverNScale := by
  refine IsBigO.of_bound (200 : ℝ) ?_
  have hle_seq : ∀ᶠ n : ℕ in atTop,
      involSecondCorrScale (involSaddleRadius n) ≤
        100 * (involSaddleRadius n) ^ (-(2 : ℝ)) :=
    involSaddleRadius_tendsto_atTop.eventually involSecondCorrScale_le_rpow_eventually
  have hnonneg_seq : ∀ᶠ n : ℕ in atTop,
      0 ≤ involSecondCorrScale (involSaddleRadius n) :=
    involSaddleRadius_tendsto_atTop.eventually involSecondCorrScale_nonneg_eventually
  have hr_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ involSaddleRadius n :=
    involSaddleRadius_tendsto_atTop.eventually_ge_atTop 1
  filter_upwards [hle_seq, hnonneg_seq, hr_ge_one, eventually_gt_atTop (0 : ℕ)] with
    n hle hnonneg hr1 hnpos
  let r := involSaddleRadius n
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn_eq : (n : ℝ) = r + r ^ 2 := by
    change (n : ℝ) = involSaddleAReal r
    rw [involSaddleAReal_radius]
  have hn_le : (n : ℝ) ≤ 2 * r ^ 2 := by
    rw [hn_eq]
    nlinarith [hr1]
  have hinv : r ^ (-(2 : ℝ)) ≤ 2 * ((1 : ℝ) / (n : ℝ)) := by
    rw [Real.rpow_neg hrpos.le]
    field_simp [hrpos.ne', hnRpos.ne']
    have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
      exact (Real.rpow_natCast r 2).symm
    rw [← hr2_rpow]
    nlinarith [hn_le]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  dsimp [involOneOverNScale]
  rw [norm_div, norm_one, Complex.norm_natCast]
  calc
    involSecondCorrScale (involSaddleRadius n) ≤ 100 * r ^ (-(2 : ℝ)) := by
      simpa [r] using hle
    _ ≤ 100 * (2 * ((1 : ℝ) / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 200 * (1 / (n : ℝ)) := by ring

lemma invol_saddleCorrection_radius_diff_eq
    (n : ℕ) (_hnpos : 0 < n) (hr1 : 1 ≤ involSaddleRadius n) :
    (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
        (involSaddleRadius n) : ℂ) + (1 : ℂ) / (6 * (n : ℂ)) =
      (((3 * (involSaddleRadius n) ^ 2 + 6 * involSaddleRadius n + 1) /
        (12 * involSaddleRadius n * (1 + 2 * involSaddleRadius n) ^ 3 *
          (1 + involSaddleRadius n)) : ℝ) : ℂ) := by
  let r := involSaddleRadius n
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hn_eq : (n : ℝ) = r + r ^ 2 := by
    change (n : ℝ) = involSaddleAReal r
    rw [involSaddleAReal_radius]
  have hreal :
      saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real r +
        (1 : ℝ) / (6 * (n : ℝ)) =
        (3 * r ^ 2 + 6 * r + 1) /
          (12 * r * (1 + 2 * r) ^ 3 * (1 + r)) := by
    rw [invol_saddleCorrection_eq hrpos.ne']
    rw [hn_eq]
    have h1r : 1 + r ≠ 0 := by positivity
    have h12r : 1 + 2 * r ≠ 0 := by positivity
    field_simp [hrpos.ne', h1r, h12r]
    ring
  have hcomplex :
      (1 : ℂ) / (6 * (n : ℂ)) = (((1 : ℝ) / (6 * (n : ℝ))) : ℂ) := by
    norm_num
  change (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real r : ℂ) +
      (1 : ℂ) / (6 * (n : ℂ)) = _
  rw [hcomplex]
  exact_mod_cast hreal

lemma invol_saddleCorrection_radius_isLittleO_one_over_n :
    (fun n : ℕ =>
      (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
        (involSaddleRadius n) : ℂ) + (1 : ℂ) / (6 * (n : ℂ)))
      =o[atTop] involOneOverNScale := by
  let u : ℕ → ℂ := fun n =>
    (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
      (involSaddleRadius n) : ℂ) + (1 : ℂ) / (6 * (n : ℂ))
  let c : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ)
  have hcpos : ∀ᶠ n in atTop, 0 < c n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hn
    exact div_pos zero_lt_one hnRpos
  have hdiv : Tendsto (fun n : ℕ => ‖u n‖ / c n) atTop (𝓝 0) := by
    have hrtop : Tendsto (fun n : ℕ => (involSaddleRadius n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp involSaddleRadius_tendsto_atTop
    refine squeeze_zero' ?_ ?_ hrtop
    · filter_upwards [hcpos] with n hcn
      exact div_nonneg (norm_nonneg _) hcn.le
    · have hr_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ involSaddleRadius n :=
        involSaddleRadius_tendsto_atTop.eventually_ge_atTop 1
      filter_upwards [eventually_gt_atTop (0 : ℕ), hr_ge_one] with n hnpos hr1
      let r := involSaddleRadius n
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
      have hn_eq : (n : ℝ) = r + r ^ 2 := by
        change (n : ℝ) = involSaddleAReal r
        rw [involSaddleAReal_radius]
      have hdiff := invol_saddleCorrection_radius_diff_eq n hnpos hr1
      have hreal_nonneg :
          0 ≤ (3 * r ^ 2 + 6 * r + 1) /
            (12 * r * (1 + 2 * r) ^ 3 * (1 + r)) := by positivity
      have hnorm : ‖u n‖ =
          (3 * r ^ 2 + 6 * r + 1) /
            (12 * r * (1 + 2 * r) ^ 3 * (1 + r)) := by
        change ‖(saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
          (involSaddleRadius n) : ℂ) + (1 : ℂ) / (6 * (n : ℂ))‖ = _
        rw [hdiff]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hreal_nonneg]
      rw [hnorm]
      have hratio : ((3 * r ^ 2 + 6 * r + 1) /
          (12 * r * (1 + 2 * r) ^ 3 * (1 + r))) / c n =
          (3 * r ^ 2 + 6 * r + 1) / (12 * (1 + 2 * r) ^ 3) := by
        dsimp [c]
        rw [hn_eq]
        have h1r : 1 + r ≠ 0 := by positivity
        have h12r : 1 + 2 * r ≠ 0 := by positivity
        field_simp [hrpos.ne', h1r, h12r]
      rw [hratio]
      have hnum : 3 * r ^ 2 + 6 * r + 1 ≤ 10 * r ^ 2 := by nlinarith [hr1]
      calc
        (3 * r ^ 2 + 6 * r + 1) / (12 * (1 + 2 * r) ^ 3)
            ≤ (10 * r ^ 2) / (12 * (1 + 2 * r) ^ 3) := by
              exact div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ r⁻¹ := by
          field_simp [hrpos.ne']
          ring_nf
          nlinarith [hr1, show 0 ≤ r ^ 2 by positivity, show 0 ≤ r ^ 3 by positivity]
  have hmain := complex_isLittleO_of_norm_div_tendsto_zero_nat u c hcpos hdiv
  refine (hmain.congr_left ?_).congr_right ?_
  · intro n
    simp [u]
  · intro n
    simp [c, involOneOverNScale]

/--
The single remaining analytical gap for this add-on: the second-order Hayman
verification for involutions (local L1 expansion through order six, tail bound
on the correction scale, and the final reduction of the signed correction to
`-1/(6n)`).  Once this estimate is supplied, the wrapper and final theorem below
are pure projections.
-/
theorem invol_secondOrder_gap :
    ∃ h2 : SecondOrderHAdmissible involHAdmissible,
      h2.b3 = involSaddleB3Real ∧
      h2.b4 = involSaddleB4Real ∧
      h2.corrScale = involSecondCorrScale ∧
      (fun n : ℕ => involSecondOrderOneOverNError n)
        =o[atTop] involOneOverNScale := by
  let h2 := involSecondOrderHAdmissibleCandidate
  have hcoeff_raw :=
    coeff_secondOrder_saddle involHAdmissible h2 involHAdmissibleSaddleSequence
  have hcoeff_corr :
      (fun n : ℕ =>
        involSeries.coeff n / involSecondOrderSaddleScale n -
          (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
            (involSaddleRadius n) : ℂ)))
        =o[atTop]
      (fun n : ℕ => (involSecondCorrScale (involSaddleRadius n) : ℂ)) := by
    simpa [h2, involSecondOrderSaddleScale, HAdmissible.B, involHAdmissible,
      involHAdmissibleSaddleSequence, involSecondOrderHAdmissibleCandidate,
      involSecondCorrScale] using hcoeff_raw
  have hcoeff_one_over_n :
      (fun n : ℕ =>
        involSeries.coeff n / involSecondOrderSaddleScale n -
          (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
            (involSaddleRadius n) : ℂ)))
        =o[atTop] involOneOverNScale :=
    hcoeff_corr.trans_isBigO involSecondCorrScale_saddleRadius_isBigO_one_over_n
  have hcorr := invol_saddleCorrection_radius_isLittleO_one_over_n
  have hsum := hcoeff_one_over_n.add hcorr
  refine ⟨h2, rfl, rfl, rfl, ?_⟩
  refine hsum.congr_left ?_
  intro n
  simp [involSecondOrderOneOverNError, involCoeffC, involSecondOrderSaddleScale,
    involSeries, PowerSeries.coeff_toFMLS, involCarrier_coeff, involCoeffR]
  ring

/-- The produced second-order H-admissible involution instance. -/
def involSecondOrderHAdmissible : SecondOrderHAdmissible involHAdmissible :=
  Classical.choose invol_secondOrder_gap

lemma involSecondOrderHAdmissible_b3 :
    involSecondOrderHAdmissible.b3 = involSaddleB3Real :=
  (Classical.choose_spec invol_secondOrder_gap).1

lemma involSecondOrderHAdmissible_b4 :
    involSecondOrderHAdmissible.b4 = involSaddleB4Real :=
  (Classical.choose_spec invol_secondOrder_gap).2.1

end InvolutionHAdmissible
end
end

/-!
# Third-order saddle data for involutions

This file instantiates the third-order Hayman wrapper for
`exp (z + z^2 / 2)`.  The fifth and sixth logarithmic saddle derivatives are
`b₅(r)=r+16r²` and `b₆(r)=r+32r²`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

noncomputable section

namespace InvolutionHAdmissible

private lemma involSaddleBReal_pos_of_ge_one_p2m2 {r : ℝ} (hr : 1 ≤ r) :
    0 < involSaddleBReal r := by
  unfold involSaddleBReal
  nlinarith [hr, sq_nonneg r]

private lemma invol_sqrtB_ge_r_p2m2 {r : ℝ} (hr : 1 ≤ r) :
    r ≤ Real.sqrt (involSaddleBReal r) := by
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := by
    unfold involSaddleBReal
    nlinarith [sq_nonneg r]
  exact Real.le_sqrt_of_sq_le hb_ge

private lemma invol_b_ge_r_sq {r : ℝ} (_hr : 1 ≤ r) :
    r ^ 2 ≤ involSaddleBReal r := by
  unfold involSaddleBReal
  nlinarith [sq_nonneg r]

private lemma invol_b_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(involSaddleBReal r : ℂ)‖ = involSaddleBReal r := by
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one_p2m2 hr
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]

private lemma invol_sqrtB_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(Real.sqrt (involSaddleBReal r) : ℂ)‖ =
      Real.sqrt (involSaddleBReal r) := by
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one_p2m2 hr
  have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt_pos]

private lemma invol_b3_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ involSaddleB3Real r := by
  unfold involSaddleB3Real
  nlinarith [hr, sq_nonneg r]

private lemma invol_b4_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ involSaddleB4Real r := by
  unfold involSaddleB4Real
  nlinarith [hr, sq_nonneg r]

private lemma invol_b5_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ involSaddleB5Real r := by
  unfold involSaddleB5Real
  nlinarith [hr, sq_nonneg r]

private lemma invol_b6_nonneg_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ involSaddleB6Real r := by
  unfold involSaddleB6Real
  nlinarith [hr, sq_nonneg r]

private lemma invol_b3_le {r : ℝ} (hr : 1 ≤ r) :
    involSaddleB3Real r ≤ 5 * r ^ 2 := by
  unfold involSaddleB3Real
  nlinarith [hr]

private lemma invol_b4_le {r : ℝ} (hr : 1 ≤ r) :
    involSaddleB4Real r ≤ 9 * r ^ 2 := by
  unfold involSaddleB4Real
  nlinarith [hr]

private lemma invol_b5_le {r : ℝ} (hr : 1 ≤ r) :
    involSaddleB5Real r ≤ 17 * r ^ 2 := by
  unfold involSaddleB5Real
  nlinarith [hr]

private lemma invol_b6_le {r : ℝ} (hr : 1 ≤ r) :
    involSaddleB6Real r ≤ 33 * r ^ 2 := by
  unfold involSaddleB6Real
  nlinarith [hr]

private lemma invol_term_b6_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    |involSaddleB6Real r| / (involSaddleBReal r) ^ 3 ≤
      100 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB6Real involSaddleBReal
  have hnum_nonneg : 0 ≤ r + 32 * r ^ 2 := by positivity
  rw [abs_of_nonneg hnum_nonneg]
  field_simp [hrpos.ne']
  ring_nf
  have hdiff : 0 ≤ 99 * r ^ 2 + 568 * r ^ 3 + 1200 * r ^ 4 + 800 * r ^ 5 := by
    positivity
  nlinarith [hdiff]

private lemma invol_term_b3b5_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4 ≤
      1000 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB3Real involSaddleB5Real involSaddleBReal
  have hnum_nonneg : 0 ≤ (r + 4 * r ^ 2) * (r + 16 * r ^ 2) := by positivity
  rw [abs_of_nonneg hnum_nonneg]
  field_simp [hrpos.ne']
  ring_nf
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
    show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
    show 0 ≤ r ^ 7 by positivity, show 0 ≤ r ^ 8 by positivity]

private lemma invol_term_b4sq_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4 ≤
      1000 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB4Real involSaddleBReal
  field_simp [hrpos.ne']
  ring_nf
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
    show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
    show 0 ≤ r ^ 7 by positivity, show 0 ≤ r ^ 8 by positivity]

private lemma invol_term_b3sqb4_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
        (involSaddleBReal r) ^ 5 ≤
      1000 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB3Real involSaddleB4Real involSaddleBReal
  have hb4_nonneg : 0 ≤ r + 8 * r ^ 2 := by positivity
  rw [abs_of_nonneg hb4_nonneg]
  field_simp [hrpos.ne']
  ring_nf
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
    show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
    show 0 ≤ r ^ 7 by positivity, show 0 ≤ r ^ 8 by positivity,
    show 0 ≤ r ^ 9 by positivity, show 0 ≤ r ^ 10 by positivity]

private lemma invol_term_b3four_le_rpow {r : ℝ} (hr : 1 ≤ r) :
    (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6 ≤
      1000 * r ^ (-(2 : ℝ)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [Real.rpow_neg hrpos.le]
  rw [show r ^ (2 : ℝ) = r ^ 2 by exact Real.rpow_natCast r 2]
  unfold involSaddleB3Real involSaddleBReal
  field_simp [hrpos.ne']
  ring_nf
  nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity, show 0 ≤ r ^ 4 by positivity,
    show 0 ≤ r ^ 5 by positivity, show 0 ≤ r ^ 6 by positivity,
    show 0 ≤ r ^ 7 by positivity, show 0 ≤ r ^ 8 by positivity,
    show 0 ≤ r ^ 9 by positivity, show 0 ≤ r ^ 10 by positivity,
    show 0 ≤ r ^ 11 by positivity, show 0 ≤ r ^ 12 by positivity]

lemma invol_saddleThirdCorrectionScale_le_second :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in atTop,
        saddleThirdCorrectionScale involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r ≤ K * involThirdCorrScale r := by
  refine ⟨200000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_lower_eventually] with
    r hr hsecondLower
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hαpos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by positivity
  have hsecond_pos : 0 < involSecondCorrScale r := lt_of_lt_of_le hαpos hsecondLower
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one_p2m2 hr
  have hdiv_nonneg₁ :
      0 ≤ |involSaddleB6Real r| / (involSaddleBReal r) ^ 3 := by positivity
  have hdiv_nonneg₂ :
      0 ≤ |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4 := by
    positivity
  have hdiv_nonneg₃ :
      0 ≤ (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4 := by positivity
  have hdiv_nonneg₄ :
      0 ≤ (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
          (involSaddleBReal r) ^ 5 := by
    positivity
  have hdiv_nonneg₅ :
      0 ≤ (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6 := by positivity
  have hterm₁ := invol_term_b6_le_rpow hr
  have hterm₂ := invol_term_b3b5_le_rpow hr
  have hterm₃ := invol_term_b4sq_le_rpow hr
  have hterm₄ := invol_term_b3sqb4_le_rpow hr
  have hterm₅ := invol_term_b3four_le_rpow hr
  have hthird :
      |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
        ≤ 4100 * r ^ (-(2 : ℝ)) := by
    nlinarith
  have hthird_second :
      |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
        ≤ 100000 * involSecondCorrScale r := by
    calc
      |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
          ≤ 4100 * r ^ (-(2 : ℝ)) := hthird
      _ ≤ 100000 * involSecondCorrScale r := by
        nlinarith
  have htarget :
      saddleCorrectionScale involSaddleBReal involSaddleB3Real involSaddleB4Real r
        + |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
      ≤ 200000 * involThirdCorrScale r := by
    change involSecondCorrScale r
        + |involSaddleB6Real r| / (involSaddleBReal r) ^ 3
        + |involSaddleB3Real r * involSaddleB5Real r| / (involSaddleBReal r) ^ 4
        + (involSaddleB4Real r) ^ 2 / (involSaddleBReal r) ^ 4
        + (involSaddleB3Real r) ^ 2 * |involSaddleB4Real r| /
            (involSaddleBReal r) ^ 5
        + (involSaddleB3Real r) ^ 4 / (involSaddleBReal r) ^ 6
      ≤ 200000 * involThirdCorrScale r
    unfold involThirdCorrScale
    nlinarith [hthird_second, hsecond_pos.le]
  simpa [saddleThirdCorrectionScale, involThirdCorrScale] using htarget

private def involThirdGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
      |x| ^ 9 + |x| ^ 10 + |x| ^ 12)

private lemma involThirdGaussianDom_nonneg (x : ℝ) : 0 ≤ involThirdGaussianDom x := by
  unfold involThirdGaussianDom
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

private lemma involThirdGaussianDom_integrable : Integrable involThirdGaussianDom := by
  unfold involThirdGaussianDom
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

private lemma involThirdGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, involThirdGaussianDom x := by
  exact integral_nonneg (fun x => involThirdGaussianDom_nonneg x)

private lemma involThirdGaussianDom_continuous : Continuous involThirdGaussianDom := by
  unfold involThirdGaussianDom
  fun_prop

private lemma involThirdGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, involThirdGaussianDom x) ≤ ∫ x : ℝ, involThirdGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral involThirdGaussianDom_integrable
    (Eventually.of_forall involThirdGaussianDom_nonneg)

private lemma invol_third_extra5_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((involSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖ ≤
        10 * |x| ^ 5 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < involSaddleBReal r := involSaddleBReal_pos_of_ge_one_p2m2 hr
  have hsqrt_pos : 0 < Real.sqrt (involSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r_p2m2 hr
  have hsqrt5_ge : r ^ 5 ≤ (Real.sqrt (involSaddleBReal r)) ^ 5 :=
    pow_le_pow_left₀ hrpos.le hsqrt_ge 5
  have hcoef :
      ‖(involSaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)‖ ≤ 1 / r ^ 3 := by
    calc
      ‖(involSaddleB5Real r : ℂ) /
          (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)‖
          = involSaddleB5Real r /
              (120 * |Real.sqrt (involSaddleBReal r)| ^ 5) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (invol_b5_nonneg_of_ge_one hr)]
            simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ = involSaddleB5Real r /
              (120 * (Real.sqrt (involSaddleBReal r)) ^ 5) := by
            rw [abs_of_pos hsqrt_pos]
      _ ≤ (17 * r ^ 2) / (120 * r ^ 5) := by
            exact div_le_div₀ (by positivity) (invol_b5_le hr) (by positivity)
              (by nlinarith [hsqrt5_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith
  calc
    ‖Complex.I * ((involSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖
        = ‖(involSaddleB5Real r : ℂ) /
            (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)‖ * |x| ^ 5 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 5 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 5)
    _ ≤ 10 * |x| ^ 5 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 5]

private lemma invol_third_extra6_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖ ≤ 10 * |x| ^ 6 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb3_ge : r ^ 6 ≤ (involSaddleBReal r) ^ 3 := by
    calc
      r ^ 6 = (r ^ 2) ^ 3 := by ring
      _ ≤ (involSaddleBReal r) ^ 3 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 3
  have hcoef :
      ‖(involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)‖
        ≤ 1 / r ^ 3 := by
    calc
      ‖(involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)‖
          = involSaddleB6Real r / (720 * (involSaddleBReal r) ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (invol_b6_nonneg_of_ge_one hr)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (33 * r ^ 2) / (720 * r ^ 6) := by
            exact div_le_div₀ (by positivity) (invol_b6_le hr) (by positivity)
              (by nlinarith [hb3_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖((involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖
        = ‖(involSaddleB6Real r : ℂ) /
            (720 * (involSaddleBReal r : ℂ) ^ 3)‖ * |x| ^ 6 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 6 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 6)
    _ ≤ 10 * |x| ^ 6 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 6]

private lemma invol_third_extra7_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * (((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
        (involSaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖ ≤
        10 * |x| ^ 7 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r_p2m2 hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hsqrt3_ge : r ^ 3 ≤ (Real.sqrt (involSaddleBReal r)) ^ 3 :=
    pow_le_pow_left₀ hrpos.le hsqrt_ge 3
  have hb2_ge : r ^ 4 ≤ (involSaddleBReal r) ^ 2 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ ≤ (involSaddleBReal r) ^ 2 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 2
  have hden_ge :
      r ^ 7 ≤ (Real.sqrt (involSaddleBReal r)) ^ 3 * (involSaddleBReal r) ^ 2 := by
    calc
      r ^ 7 = r ^ 3 * r ^ 4 := by ring
      _ ≤ (Real.sqrt (involSaddleBReal r)) ^ 3 * (involSaddleBReal r) ^ 2 :=
        mul_le_mul hsqrt3_ge hb2_ge (by positivity) (by positivity)
  have hnum_nonneg : 0 ≤ involSaddleB3Real r * involSaddleB4Real r :=
    mul_nonneg (invol_b3_nonneg_of_ge_one hr) (invol_b4_nonneg_of_ge_one hr)
  have hnum_le : involSaddleB3Real r * involSaddleB4Real r ≤ 45 * r ^ 4 := by
    calc
      involSaddleB3Real r * involSaddleB4Real r
          ≤ (5 * r ^ 2) * (9 * r ^ 2) :=
            mul_le_mul (invol_b3_le hr) (invol_b4_le hr)
              (invol_b4_nonneg_of_ge_one hr) (by positivity)
      _ = 45 * r ^ 4 := by ring
  have hcoef :
      ‖(((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
          (involSaddleBReal r : ℂ) ^ 2))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖(((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
          (involSaddleBReal r : ℂ) ^ 2))‖
          =
            (involSaddleB3Real r * involSaddleB4Real r) /
              (144 * (Real.sqrt (involSaddleBReal r)) ^ 3 *
                (involSaddleBReal r) ^ 2) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_sqrtB_norm_eq_of_ge_one hr, invol_b_norm_eq_of_ge_one hr]
      _ ≤ (45 * r ^ 4) / (144 * r ^ 7) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hden_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖Complex.I * (((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
        (involSaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖
        = ‖(((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
            (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
              (involSaddleBReal r : ℂ) ^ 2))‖ * |x| ^ 7 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 7 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 7)
    _ ≤ 10 * |x| ^ 7 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 7]

private lemma invol_third_extra8a_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
      (720 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖ ≤
        10 * |x| ^ 8 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb4_ge : r ^ 8 ≤ (involSaddleBReal r) ^ 4 := by
    calc
      r ^ 8 = (r ^ 2) ^ 4 := by ring
      _ ≤ (involSaddleBReal r) ^ 4 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 4
  have hnum_nonneg : 0 ≤ involSaddleB3Real r * involSaddleB5Real r :=
    mul_nonneg (invol_b3_nonneg_of_ge_one hr) (invol_b5_nonneg_of_ge_one hr)
  have hnum_le : involSaddleB3Real r * involSaddleB5Real r ≤ 85 * r ^ 4 := by
    calc
      involSaddleB3Real r * involSaddleB5Real r
          ≤ (5 * r ^ 2) * (17 * r ^ 2) :=
            mul_le_mul (invol_b3_le hr) (invol_b5_le hr)
              (invol_b5_nonneg_of_ge_one hr) (by positivity)
      _ = 85 * r ^ 4 := by ring
  have hcoef :
      ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
        (720 * (involSaddleBReal r : ℂ) ^ 4))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
        (720 * (involSaddleBReal r : ℂ) ^ 4))‖
          = (involSaddleB3Real r * involSaddleB5Real r) /
              (720 * (involSaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (85 * r ^ 4) / (720 * r ^ 8) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
      (720 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖
        = ‖(((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
            (720 * (involSaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ ≤ 10 * |x| ^ 8 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 8]

private lemma invol_third_extra8b_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖ ≤
        10 * |x| ^ 8 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb4_ge : r ^ 8 ≤ (involSaddleBReal r) ^ 4 := by
    calc
      r ^ 8 = (r ^ 2) ^ 4 := by ring
      _ ≤ (involSaddleBReal r) ^ 4 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 4
  have hnum_le : (involSaddleB4Real r) ^ 2 ≤ 81 * r ^ 4 := by
    calc
      (involSaddleB4Real r) ^ 2 ≤ (9 * r ^ 2) ^ 2 :=
        pow_le_pow_left₀ (invol_b4_nonneg_of_ge_one hr) (invol_b4_le hr) 2
      _ = 81 * r ^ 4 := by ring
  have hcoef :
      ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (involSaddleBReal r : ℂ) ^ 4))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (involSaddleBReal r : ℂ) ^ 4))‖
          = (involSaddleB4Real r) ^ 2 / (1152 * (involSaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sq_nonneg _)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (81 * r ^ 4) / (1152 * r ^ 8) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8‖
        = ‖((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
            (1152 * (involSaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ ≤ 10 * |x| ^ 8 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 8]

private lemma invol_third_extra9_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖ ≤
        10 * |x| ^ 9 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := invol_sqrtB_ge_r_p2m2 hr
  have hsqrt9_ge : r ^ 9 ≤ (Real.sqrt (involSaddleBReal r)) ^ 9 :=
    pow_le_pow_left₀ hrpos.le hsqrt_ge 9
  have hnum_le : (involSaddleB3Real r) ^ 3 ≤ 125 * r ^ 6 := by
    calc
      (involSaddleB3Real r) ^ 3 ≤ (5 * r ^ 2) ^ 3 :=
        pow_le_pow_left₀ (invol_b3_nonneg_of_ge_one hr) (invol_b3_le hr) 3
      _ = 125 * r ^ 6 := by ring
  have hcoef :
      ‖((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9))‖
          = (involSaddleB3Real r) ^ 3 /
              (1296 * (Real.sqrt (involSaddleBReal r)) ^ 9) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (invol_b3_nonneg_of_ge_one hr) 3)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_sqrtB_norm_eq_of_ge_one hr]
      _ ≤ (125 * r ^ 6) / (1296 * r ^ 9) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hsqrt9_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖Complex.I * ((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖
        = ‖((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
            (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9))‖ * |x| ^ 9 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 9 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 9)
    _ ≤ 10 * |x| ^ 9 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 9]

private lemma invol_third_extra10_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
      (1728 * (involSaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖ ≤
        10 * |x| ^ 10 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb5_ge : r ^ 10 ≤ (involSaddleBReal r) ^ 5 := by
    calc
      r ^ 10 = (r ^ 2) ^ 5 := by ring
      _ ≤ (involSaddleBReal r) ^ 5 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 5
  have hnum_nonneg : 0 ≤ (involSaddleB3Real r) ^ 2 * involSaddleB4Real r :=
    mul_nonneg (sq_nonneg _) (invol_b4_nonneg_of_ge_one hr)
  have hnum_le : (involSaddleB3Real r) ^ 2 * involSaddleB4Real r ≤ 225 * r ^ 6 := by
    have hb3sq : (involSaddleB3Real r) ^ 2 ≤ (5 * r ^ 2) ^ 2 :=
      pow_le_pow_left₀ (invol_b3_nonneg_of_ge_one hr) (invol_b3_le hr) 2
    calc
      (involSaddleB3Real r) ^ 2 * involSaddleB4Real r
          ≤ (5 * r ^ 2) ^ 2 * (9 * r ^ 2) :=
            mul_le_mul hb3sq (invol_b4_le hr)
              (invol_b4_nonneg_of_ge_one hr) (by positivity)
      _ = 225 * r ^ 6 := by ring
  have hcoef :
      ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
        (1728 * (involSaddleBReal r : ℂ) ^ 5)))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
        (1728 * (involSaddleBReal r : ℂ) ^ 5)))‖
          = ((involSaddleB3Real r) ^ 2 * involSaddleB4Real r) /
              (1728 * (involSaddleBReal r) ^ 5) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (225 * r ^ 6) / (1728 * r ^ 10) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb5_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
      (1728 * (involSaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖
        = ‖(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
            (1728 * (involSaddleBReal r : ℂ) ^ 5)))‖ * |x| ^ 10 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 10 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 10)
    _ ≤ 10 * |x| ^ 10 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 10]

private lemma invol_third_extra12_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (involSaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12‖ ≤
        10 * |x| ^ 12 / r ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := invol_b_ge_r_sq hr
  have hb6_ge : r ^ 12 ≤ (involSaddleBReal r) ^ 6 := by
    calc
      r ^ 12 = (r ^ 2) ^ 6 := by ring
      _ ≤ (involSaddleBReal r) ^ 6 := pow_le_pow_left₀ (sq_nonneg r) hb_ge 6
  have hnum_le : (involSaddleB3Real r) ^ 4 ≤ 625 * r ^ 8 := by
    calc
      (involSaddleB3Real r) ^ 4 ≤ (5 * r ^ 2) ^ 4 :=
        pow_le_pow_left₀ (invol_b3_nonneg_of_ge_one hr) (invol_b3_le hr) 4
      _ = 625 * r ^ 8 := by ring
  have hcoef :
      ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (involSaddleBReal r : ℂ) ^ 6))‖ ≤ 1 / r ^ 3 := by
    calc
      ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (involSaddleBReal r : ℂ) ^ 6))‖
          = (involSaddleB3Real r) ^ 4 / (31104 * (involSaddleBReal r) ^ 6) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (invol_b3_nonneg_of_ge_one hr) 4)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [invol_b_norm_eq_of_ge_one hr]
      _ ≤ (625 * r ^ 8) / (31104 * r ^ 12) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb6_ge])
      _ ≤ 1 / r ^ 3 := by
            field_simp [hrpos.ne']
            nlinarith [hr]
  calc
    ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (involSaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12‖
        = ‖((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
            (31104 * (involSaddleBReal r : ℂ) ^ 6))‖ * |x| ^ 12 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / r ^ 3) * |x| ^ 12 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 12)
    _ ≤ 10 * |x| ^ 12 / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [pow_nonneg (abs_nonneg x) 12]

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

private lemma invol_third_extra_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
        involSaddleB5Real involSaddleB6Real r x -
      saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x‖
      ≤ 1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
        |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 3 := by
  let T5 : ℂ :=
    Complex.I * ((involSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5
  let T6 : ℂ :=
    -((involSaddleB6Real r : ℂ) / (720 * (involSaddleBReal r : ℂ) ^ 3)) *
      (x : ℂ) ^ 6
  let T7 : ℂ :=
    -Complex.I * (((involSaddleB3Real r * involSaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 3 *
        (involSaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7
  let T8a : ℂ :=
    (((involSaddleB3Real r * involSaddleB5Real r : ℝ) : ℂ) /
      (720 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T8b : ℂ :=
    ((((involSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (involSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T9 : ℂ :=
    Complex.I * ((((involSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (involSaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9
  let T10 : ℂ :=
    -(((((involSaddleB3Real r) ^ 2 * involSaddleB4Real r : ℝ) : ℂ) /
      (1728 * (involSaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)
  let T12 : ℂ :=
    ((((involSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (involSaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12
  have h5 : ‖T5‖ ≤ 10 * |x| ^ 5 / r ^ 3 := by
    dsimp [T5]
    exact invol_third_extra5_norm_le (r := r) (x := x) hr
  have h6 : ‖T6‖ ≤ 10 * |x| ^ 6 / r ^ 3 := by
    dsimp [T6]
    simpa using invol_third_extra6_norm_le (r := r) (x := x) hr
  have h7 : ‖T7‖ ≤ 10 * |x| ^ 7 / r ^ 3 := by
    dsimp [T7]
    simpa [norm_neg] using invol_third_extra7_norm_le (r := r) (x := x) hr
  have h8a : ‖T8a‖ ≤ 10 * |x| ^ 8 / r ^ 3 := by
    dsimp [T8a]
    exact invol_third_extra8a_norm_le (r := r) (x := x) hr
  have h8b : ‖T8b‖ ≤ 10 * |x| ^ 8 / r ^ 3 := by
    dsimp [T8b]
    exact invol_third_extra8b_norm_le (r := r) (x := x) hr
  have h9 : ‖T9‖ ≤ 10 * |x| ^ 9 / r ^ 3 := by
    dsimp [T9]
    exact invol_third_extra9_norm_le (r := r) (x := x) hr
  have h10 : ‖T10‖ ≤ 10 * |x| ^ 10 / r ^ 3 := by
    dsimp [T10]
    simpa [norm_neg] using invol_third_extra10_norm_le (r := r) (x := x) hr
  have h12 : ‖T12‖ ≤ 10 * |x| ^ 12 / r ^ 3 := by
    dsimp [T12]
    exact invol_third_extra12_norm_le (r := r) (x := x) hr
  have hdiff :
      saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r x -
        saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x =
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
    _ ≤ 10 * |x| ^ 5 / r ^ 3 + 10 * |x| ^ 6 / r ^ 3 +
          10 * |x| ^ 7 / r ^ 3 + 10 * |x| ^ 8 / r ^ 3 +
          10 * |x| ^ 8 / r ^ 3 + 10 * |x| ^ 9 / r ^ 3 +
          10 * |x| ^ 10 / r ^ 3 + 10 * |x| ^ 12 / r ^ 3 := by
          nlinarith
    _ ≤ 1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
          |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 3 := by
          have hr3pos : 0 < r ^ 3 := by positivity
          field_simp [hr3pos.ne']
          nlinarith [hnonneg, pow_nonneg (abs_nonneg x) 5,
            pow_nonneg (abs_nonneg x) 6, pow_nonneg (abs_nonneg x) 7,
            pow_nonneg (abs_nonneg x) 8, pow_nonneg (abs_nonneg x) 9,
            pow_nonneg (abs_nonneg x) 10, pow_nonneg (abs_nonneg x) 12]

private lemma invol_local_third_extra_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
              involSaddleB5Real involSaddleB6Real r x -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
          involSecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, involThirdGaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact involThirdGaussianDom_integral_nonneg
  have hupper_tendsto :
      Tendsto (fun r : ℝ => (1000 * M * (27 / 16 : ℝ)) / r)
        atTop (𝓝 0) := by
    have hinv : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv, mul_assoc] using
      hinv.const_mul (1000 * M * (27 / 16 : ℝ))
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, involSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
              involSaddleB5Real involSaddleB6Real r x -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_lower_eventually,
      involSecondCorrScale_pos_eventually] with r hr hcorrLower hcorrPos
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r x -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
    let G : ℝ → ℝ := fun x => (1000 / r ^ 3) * involThirdGaussianDom x
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hLnonneg : 0 ≤ L := by
      dsimp [L, involSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ G x := by
      intro x hx
      have hdiff := invol_third_extra_norm_le (r := r) (x := x) hr
      dsimp [F, G, involThirdGaussianDom]
      rw [norm_mul]
      have hgauss :
          ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
        rw [Complex.norm_exp]
        congr 1
        simp [pow_two]
      rw [hgauss]
      calc
        Real.exp (-(x ^ 2) / 2) *
            ‖saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x‖
            ≤ Real.exp (-(x ^ 2) / 2) *
                (1000 * (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                  |x| ^ 9 + |x| ^ 10 + |x| ^ 12) / r ^ 3) :=
              mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
        _ = 1000 / r ^ 3 *
            (Real.exp (-(x ^ 2) / 2) *
              (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                |x| ^ 9 + |x| ^ 10 + |x| ^ 12)) := by ring
    have hFint : IntervalIntegrable F volume (-L) L := by
      have hcont : Continuous F := by
        dsimp [F]
        simp only [saddleThirdPoly, saddleSecondPoly, involSaddleBReal, involSaddleB3Real,
          involSaddleB4Real, involSaddleB5Real, involSaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hGint : IntervalIntegrable G volume (-L) L := by
      exact (involThirdGaussianDom_continuous.const_mul (1000 / r ^ 3)).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤ (1000 / r ^ 3) * M := by
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, G x :=
          intervalIntegral.integral_mono_on hle hFint hGint hpoint
        _ = (1000 / r ^ 3) * (∫ x in -L..L, involThirdGaussianDom x) := by
          dsimp [G]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (1000 / r ^ 3) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact involThirdGaussianDom_window_le_integral hLnonneg)
            (div_nonneg (by norm_num) (by positivity))
    have hnum_nonneg : 0 ≤ (1000 / r ^ 3) * M :=
      mul_nonneg (div_nonneg (by norm_num) (by positivity)) hM_nonneg
    have hscale_pos : 0 < (16 / 27 : ℝ) * r ^ (-(2 : ℝ)) := by positivity
    have hmain :
        (∫ x in -L..L, F x) / involSecondCorrScale r ≤
          ((1000 / r ^ 3) * M) / ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) := by
      calc
        (∫ x in -L..L, F x) / involSecondCorrScale r
            ≤ ((1000 / r ^ 3) * M) / involSecondCorrScale r :=
              div_le_div_of_nonneg_right hIntBound hcorrPos.le
        _ ≤ ((1000 / r ^ 3) * M) / ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) :=
            div_le_div_of_nonneg_left hnum_nonneg hscale_pos hcorrLower
    calc
      ((∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
              involSaddleB5Real involSaddleB6Real r x -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
          involSecondCorrScale r)
          = (∫ x in -L..L, F x) / involSecondCorrScale r := by rfl
      _ ≤ ((1000 / r ^ 3) * M) / ((16 / 27 : ℝ) * r ^ (-(2 : ℝ))) := hmain
      _ = (1000 * M * (27 / 16 : ℝ)) / r := by
        rw [Real.rpow_neg hrpos.le]
        field_simp [hrpos.ne']
        ring_nf
        norm_num

theorem invol_local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
          (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x)‖) /
          involThirdCorrScale r)
      atTop (𝓝 0) := by
  unfold involThirdCorrScale
  let T : ℝ → ℝ := fun r =>
    (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
      (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
            involSaddleB5Real involSaddleB6Real r x)‖) / involSecondCorrScale r
  let S : ℝ → ℝ := fun r =>
    (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
      (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
      involSecondCorrScale r
  let E : ℝ → ℝ := fun r =>
    (∫ x in -(involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))..
      (involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r x -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖) /
      involSecondCorrScale r
  change Tendsto T atTop (𝓝 0)
  have hsecond := invol_local_second_L1
  have hextra := invol_local_third_extra_L1
  have hsum : Tendsto (fun r : ℝ => S r + E r) atTop (𝓝 0) := by
    simpa [S, E] using hsecond.add hextra
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, involSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    dsimp [T]
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), involSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r)
    let FT : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
            involSaddleB5Real involSaddleB6Real r x)‖
    let FS : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
            (x / Real.sqrt (involSaddleBReal r)) -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
    let FE : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
          involSaddleB5Real involSaddleB6Real r x -
          saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖
    have hLnonneg : 0 ≤ L := by
      dsimp [L, involSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, FT x ≤ FS x + FE x := by
      intro x hx
      dsimp [FT, FS, FE]
      calc
        ‖Complex.exp (-(x ^ 2) / 2) *
          (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
              (x / Real.sqrt (involSaddleBReal r)) -
            saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
              involSaddleB5Real involSaddleB6Real r x)‖
            =
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x) -
            Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x -
                saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ := by
              congr 1
              ring
        _ ≤
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio involFun involSaddleAReal involSaddleBReal r
                (x / Real.sqrt (involSaddleBReal r)) -
              saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ +
          ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly involSaddleBReal involSaddleB3Real involSaddleB4Real
                involSaddleB5Real involSaddleB6Real r x -
                saddleSecondPoly involSaddleBReal involSaddleB3Real involSaddleB4Real r x)‖ :=
            norm_sub_le _ _
    have hFTint : IntervalIntegrable FT volume (-L) L := by
      have hcont : Continuous FT := by
        dsimp [FT]
        simp only [invol_saddleLocalRatio_eq]
        simp only [saddleThirdPoly, saddleSecondPoly, involLocalExponent,
          ExpStirling.expLocalRemainder, involFun, involSaddleAReal,
          involSaddleBReal, involSaddleB3Real, involSaddleB4Real, involSaddleB5Real,
          involSaddleB6Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hFSint : IntervalIntegrable FS volume (-L) L := by
      have hcont : Continuous FS := by
        dsimp [FS]
        simp only [invol_saddleLocalRatio_eq]
        simp only [saddleSecondPoly, involLocalExponent, ExpStirling.expLocalRemainder,
          involFun, involSaddleAReal, involSaddleBReal, involSaddleB3Real,
          involSaddleB4Real]
        fun_prop
      exact hcont.intervalIntegrable _ _
    have hFEint : IntervalIntegrable FE volume (-L) L := by
      have hcont : Continuous FE := by
        dsimp [FE]
        simp only [saddleThirdPoly, saddleSecondPoly, involSaddleBReal, involSaddleB3Real,
          involSaddleB4Real, involSaddleB5Real, involSaddleB6Real]
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
        (∫ x in -L..L, FT x) / involSecondCorrScale r ≤
          ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            involSecondCorrScale r :=
      div_le_div_of_nonneg_right hInt hcorr.le
    calc
      T r = (∫ x in -L..L, FT x) / involSecondCorrScale r := by rfl
      _ ≤ ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            involSecondCorrScale r := hdiv
      _ = S r + E r := by
        dsimp [S, E, FS, FE, L]
        ring

def involThirdOrderHAdmissible :
    ThirdOrderHAdmissible involHAdmissible involSecondOrderHAdmissible where
  b5 := involSaddleB5Real
  b6 := involSaddleB6Real
  corrScale3 := involThirdCorrScale
  corrScale3_pos := by
    simpa [involHAdmissible, involThirdCorrScale] using involSecondCorrScale_pos_eventually
  corrScale3_tendsto_zero := by
    simpa [involHAdmissible, involThirdCorrScale] using involSecondCorrScale_tendsto_zero
  corrScale3_dominates_correction := by
    simpa [involHAdmissible, involThirdCorrScale, involSecondOrderHAdmissible_b3,
      involSecondOrderHAdmissible_b4] using invol_saddleThirdCorrectionScale_le_second
  local_third_L1 := by
    simpa [involHAdmissible, involThirdCorrScale, involSecondOrderHAdmissible_b3,
      involSecondOrderHAdmissible_b4] using invol_local_third_L1
  tail_third_uniform := by
    simpa [involHAdmissible, involThirdCorrScale] using invol_tail_second_uniform

theorem invol_coeff_thirdOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      involSeries.coeff n / involSecondOrderSaddleScale n -
        (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
          (involSaddleRadius n) : ℂ) +
          (saddleThirdCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
            involSaddleB5Real involSaddleB6Real (involSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (involThirdCorrScale (involSaddleRadius n) : ℂ)) := by
  have h :=
    coeff_thirdOrder_saddle
      involHAdmissible involSecondOrderHAdmissible involThirdOrderHAdmissible
      involHAdmissibleSaddleSequence
  simpa [involSecondOrderSaddleScale, HAdmissible.B, involHAdmissible,
    involHAdmissibleSaddleSequence, involSecondOrderHAdmissible_b3,
    involSecondOrderHAdmissible_b4, involThirdCorrScale] using h

end InvolutionHAdmissible
end

open InvolutionHAdmissible
open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
theorem solution :
    (fun n : ℕ =>
      involCoeffC n / involSecondOrderSaddleScale n -
        (1 + (saddleCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
          (involSaddleRadius n) : ℂ) +
          (saddleThirdCorrection involSaddleBReal involSaddleB3Real involSaddleB4Real
            involSaddleB5Real involSaddleB6Real (involSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (involThirdCorrScale (involSaddleRadius n) : ℂ)) := by
  refine invol_coeff_thirdOrder_saddle_from_HAdmissible.congr_left ?_
  intro n
  simp [involCoeffC, involSeries, PowerSeries.coeff_toFMLS, involCarrier_coeff]
