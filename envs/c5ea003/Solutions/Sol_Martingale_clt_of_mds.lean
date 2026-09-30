-- Prove2me | solution 1 for Martingale.clt_of_mds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:07:26.752223+00:00
-- url     : https://prove2.me/submissions/ec6675bc-b366-4485-8a63-169318a57517

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_Martingale_clt_of_mds_array

/- The finite maximum tail bound is root-authored. Normalization, Lindeberg
integration, and conclusion are by truncation_resume. The array CLT is used
through its freshly captured accepted public theorem. -/

section Component1
open scoped BigOperators

namespace MdsLindeberg

lemma finiteMax_le_tail (n : ℕ) (x : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (⨆ k : Fin n, |x k.val|) ≤
      ε + ε⁻¹ * ∑ k ∈ Finset.range n, if ε ≤ |x k| then x k ^ 2 else 0 := by
  classical
  have htail : ∀ k, 0 ≤ (if ε ≤ |x k| then x k ^ 2 else 0) :=
    fun k => by split_ifs <;> positivity
  have hsum : 0 ≤ ∑ k ∈ Finset.range n, if ε ≤ |x k| then x k ^ 2 else 0 :=
    Finset.sum_nonneg (fun k _ => htail k)
  apply Real.iSup_le
  · intro k
    by_cases hk : ε ≤ |x k.val|
    · have hsingle : x k.val ^ 2 ≤
          ∑ j ∈ Finset.range n, if ε ≤ |x j| then x j ^ 2 else 0 := by
        simpa only [if_pos hk] using
          (Finset.single_le_sum (fun j _ => htail j) (Finset.mem_range.mpr k.isLt))
      have hscalar : |x k.val| ≤ ε⁻¹ * x k.val ^ 2 := by
        rw [← div_eq_inv_mul, le_div_iff₀ hε]
        nlinarith [sq_abs (x k.val), mul_nonneg (abs_nonneg (x k.val))
          (sub_nonneg.mpr hk)]
      have hmono := mul_le_mul_of_nonneg_left hsingle (inv_nonneg.mpr hε.le)
      linarith
    · have hsmall := lt_of_not_ge hk
      have := mul_nonneg (inv_nonneg.mpr hε.le) hsum
      linarith
  · positivity

end MdsLindeberg
end Component1

section Component2
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory

noncomputable section

namespace MdsLindeberg

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

def normalizedIncrement (D : ℕ → Ω → ℝ) (n i : ℕ) (ω : Ω) : ℝ :=
  (Real.sqrt n)⁻¹ * D i ω

def lindebergTerm (D : ℕ → Ω → ℝ) (ε : ℝ) (n i : ℕ) (ω : Ω) : ℝ :=
  Set.indicator {ω' | ε * Real.sqrt n ≤ |D i ω'|} (fun ω' => D i ω' ^ 2) ω

lemma normalizedIncrement_sq (D : ℕ → Ω → ℝ) (n i : ℕ) (ω : Ω) :
    normalizedIncrement D n i ω ^ 2 = (n : ℝ)⁻¹ * D i ω ^ 2 := by
  simp only [normalizedIncrement, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

lemma normalized_squareSum (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range n, normalizedIncrement D n i ω ^ 2) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, D i ω ^ 2 := by
  simp only [normalizedIncrement_sq, Finset.mul_sum]

lemma normalized_sum (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range n, normalizedIncrement D n i ω) =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, D i ω := by
  simp only [normalizedIncrement, Finset.mul_sum]

lemma measurable_normalizedIncrement (D : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (D i)) (n i : ℕ) :
    Measurable (normalizedIncrement D n i) :=
  measurable_const.mul (hmeas i)

lemma adapted_normalizedIncrement (ℱ : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hadapt : Adapted ℱ D) (n i : ℕ) :
    Measurable[ℱ i] (normalizedIncrement D n i) :=
  measurable_const.mul (hadapt i)

lemma integrable_normalizedIncrement (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hL2 : ∀ i, MemLp (D i) 2 P) (n i : ℕ) :
    Integrable (normalizedIncrement D n i) P :=
  ((hL2 i).integrable (by norm_num)).const_mul _

lemma condExp_normalizedIncrement (P : Measure Ω) (ℱ : Filtration ℕ m0)
    (D : ℕ → Ω → ℝ) (hmds : ∀ i, P[D (i + 1) | ℱ i] =ᵐ[P] 0) (n i : ℕ) :
    P[normalizedIncrement D n (i + 1) | ℱ i] =ᵐ[P] 0 := by
  have h := condExp_smul (μ := P) (Real.sqrt n)⁻¹ (D (i + 1)) (ℱ i)
  filter_upwards [h, hmds i] with ω hω hz
  change P[(Real.sqrt n)⁻¹ • D (i + 1) | ℱ i] ω = 0
  simpa only [Pi.smul_apply, smul_eq_mul, hz, Pi.zero_apply, mul_zero] using hω

lemma integral_normalizedIncrement_zero (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (hcent : ∫ ω, D 0 ω ∂P = 0) (n : ℕ) :
    ∫ ω, normalizedIncrement D n 0 ω ∂P = 0 := by
  simp only [normalizedIncrement, integral_const_mul, hcent, mul_zero]

lemma integrable_lindebergTerm (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (D i)) (hL2 : ∀ i, MemLp (D i) 2 P)
    (ε : ℝ) (n i : ℕ) : Integrable (lindebergTerm D ε n i) P := by
  exact (hL2 i).integrable_sq.indicator (measurableSet_le measurable_const ((hmeas i).abs))

lemma normalized_tail_eq (D : ℕ → Ω → ℝ) (ε : ℝ) (hε : 0 < ε)
    (n i : ℕ) (ω : Ω) :
    (if ε ≤ |normalizedIncrement D n i ω| then normalizedIncrement D n i ω ^ 2 else 0) =
      (n : ℝ)⁻¹ * lindebergTerm D ε n i ω := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [normalizedIncrement, not_le.mpr hε]
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  have htest : (ε ≤ |normalizedIncrement D n i ω|) ↔ ε * Real.sqrt n ≤ |D i ω| := by
    rw [normalizedIncrement, abs_mul, abs_of_nonneg (inv_nonneg.mpr hs.le),
      ← div_eq_inv_mul, le_div_iff₀ hs]
  simp only [htest]
  by_cases hlarge : ε * Real.sqrt n ≤ |D i ω|
  · simp [hlarge, normalizedIncrement_sq, lindebergTerm, Set.indicator]
  · simp [hlarge, lindebergTerm, Set.indicator]

end MdsLindeberg

end
end Component2

section Component3
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory

namespace MdsLindeberg

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The finite-maximum integrability argument is adapted from our Round45 component. -/
lemma integrable_normalizedMax (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (D i))
    (hL2 : ∀ i, MemLp (D i) 2 P) (n : ℕ) :
    Integrable (fun ω => ⨆ k : Fin n, |normalizedIncrement D n k.val ω|) P := by
  have hs : Integrable (fun ω => ∑ k : Fin n, |normalizedIncrement D n k.val ω|) P :=
    integrable_finsetSum Finset.univ
      (fun k _ => (integrable_normalizedIncrement P D hL2 n k.val).abs)
  apply hs.mono' (Measurable.iSup
    (fun k : Fin n => (measurable_normalizedIncrement D hmeas n k.val).abs)).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg (fun _ => abs_nonneg _))]
  apply Real.iSup_le
  · intro k
    exact Finset.single_le_sum (fun j _ => abs_nonneg (normalizedIncrement D n j.val ω))
      (Finset.mem_univ k)
  · exact Finset.sum_nonneg (fun j _ => abs_nonneg (normalizedIncrement D n j.val ω))

lemma integral_normalizedMax_le (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (D i))
    (hL2 : ∀ i, MemLp (D i) 2 P) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (∫ ω, ⨆ k : Fin n, |normalizedIncrement D n k.val ω| ∂P) ≤
      ε + ε⁻¹ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ ω, lindebergTerm D ε n i ω ∂P) := by
  classical
  let tail : ℕ → Ω → ℝ := fun i ω =>
    if ε ≤ |normalizedIncrement D n i ω| then normalizedIncrement D n i ω ^ 2 else 0
  have htail : ∀ i, Integrable (tail i) P := by
    intro i
    have heq : tail i = fun ω => (n : ℝ)⁻¹ * lindebergTerm D ε n i ω := by
      funext ω
      exact normalized_tail_eq D ε hε n i ω
    rw [heq]
    exact (integrable_lindebergTerm P D hmeas hL2 ε n i).const_mul _
  have hsum : Integrable (fun ω => ∑ i ∈ Finset.range n, tail i ω) P :=
    integrable_finsetSum (Finset.range n) (fun i _ => htail i)
  calc
    _ ≤ ∫ ω, ε + ε⁻¹ * ∑ i ∈ Finset.range n, tail i ω ∂P :=
      integral_mono (integrable_normalizedMax P D hmeas hL2 n)
        ((integrable_const ε).add (hsum.const_mul _))
        (fun ω => finiteMax_le_tail n (fun i => normalizedIncrement D n i ω) ε hε)
    _ = _ := by
      rw [integral_add (integrable_const ε) (hsum.const_mul _), integral_const_mul,
        integral_finsetSum (Finset.range n) (fun i _ => htail i)]
      have htailint : ∀ i, (∫ ω, tail i ω ∂P) =
          (n : ℝ)⁻¹ * ∫ ω, lindebergTerm D ε n i ω ∂P := by
        intro i
        simp only [tail, normalized_tail_eq D ε hε, integral_const_mul]
      simp only [htailint, ← Finset.mul_sum]
      simp

lemma lindeberg_implies_max_negligible (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (D i))
    (hL2 : ∀ i, MemLp (D i) 2 P)
    (hlind : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ∫ ω, lindebergTerm D ε n i ω ∂P) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ ω, ⨆ k : Fin n, |normalizedIncrement D n k.val ω| ∂P)
      atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha
      (integral_nonneg fun ω => Real.iSup_nonneg (fun _ => abs_nonneg _))
  · intro b hb
    have he : 0 < b / 2 := by positivity
    have hlimit : Tendsto (fun n : ℕ => b / 2 + (b / 2)⁻¹ *
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ ω, lindebergTerm D (b / 2) n i ω ∂P))
        atTop (𝓝 (b / 2)) := by
      simpa using tendsto_const_nhds.add ((hlind (b / 2) he).const_mul ((b / 2)⁻¹))
    have hbound := hlimit.eventually (gt_mem_nhds (by linarith : b / 2 < b))
    filter_upwards [hbound] with n hn
    exact lt_of_le_of_lt (integral_normalizedMax_le P D hmeas hL2 (b / 2) he n) hn

end MdsLindeberg
end Component3

section Component4
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hadapt : Adapted ℱ D) (hmeas : ∀ i, Measurable (D i))
    (hL2 : ∀ i, MemLp (D i) 2 P)
    (hcent : ∫ ω, D 0 ω ∂P = 0)
    (hmds : ∀ i, P[D (i + 1) | ℱ i] =ᵐ[P] 0)
    (v : ℝ) (hv : 0 ≤ v)
    (hqv : TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, D i ω ^ 2) atTop (fun _ => v))
    (hlind : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ∫ ω, Set.indicator {ω' | ε * Real.sqrt n ≤ |D i ω'|} (fun ω' => D i ω' ^ 2) ω ∂P)
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, D i ω)
      atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 v.toNNReal) := by
  have hneg : Tendsto
      (fun n : ℕ => ∫ ω, ⨆ k : Fin n, |MdsLindeberg.normalizedIncrement D n k.val ω| ∂P)
      atTop (𝓝 0) :=
    MdsLindeberg.lindeberg_implies_max_negligible P D hmeas hL2 hlind
  have hvar : TendstoInMeasure P
      (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, MdsLindeberg.normalizedIncrement D n k ω ^ 2)
      atTop (fun _ => (Real.sqrt v) ^ 2) := by
    simpa only [MdsLindeberg.normalized_squareSum, Real.sq_sqrt hv] using hqv
  have hlimit := Martingale.clt_of_mds_array P ℱ (MdsLindeberg.normalizedIncrement D)
    (MdsLindeberg.measurable_normalizedIncrement D hmeas)
    (MdsLindeberg.adapted_normalizedIncrement ℱ D hadapt)
    (MdsLindeberg.integrable_normalizedIncrement P D hL2)
    (MdsLindeberg.condExp_normalizedIncrement P ℱ D hmds)
    (MdsLindeberg.integral_normalizedIncrement_zero P D hcent)
    (Real.sqrt v) (Real.sqrt_nonneg v) hneg hvar
  simpa only [MdsLindeberg.normalized_sum, Real.sq_sqrt hv] using hlimit
end Component4

