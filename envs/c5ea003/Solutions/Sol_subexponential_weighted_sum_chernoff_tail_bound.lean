-- Prove2me | solution 1 for subexponential_weighted_sum_chernoff_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-03T22:42:09.074576+00:00
-- url     : https://prove2.me/submissions/b2eb00db-7426-4ce3-8618-21118f13fcdb

/-
Solution for `subexponential_weighted_sum_chernoff_tail_bound`.

Chernoff bound for the upper tail of a weighted sum `∑ aᵢ·zᵢ` of i.i.d.
sub-exponential noise over `Measure.pi`: for any parameter `t ∈ (0, 1/ξ)`,

  `P[∑ aᵢzᵢ ≥ s] ≤ exp(−t·s + t²·(∑aᵢ²)·γ²/2)`.

Route: lintegral MGF hypothesis → Bochner integrability + MGF bound per factor
(`|t·aᵢ| ≤ t < 1/ξ`); coordinate independence via `iIndepFun_pi`; product MGF
via `iIndepFun.mgf_sum`; Markov via `measure_ge_le_exp_mul_mgf`.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Basic

open MeasureTheory ProbabilityTheory Real Set

namespace ChernoffTailAux

/-- The MGF factor `e^{l·z}` is integrable whenever the lintegral MGF bound applies. -/
lemma factor_integrable {noise : Measure ℝ} {γ ξ : ℝ}
    (hse : ∀ l : ℝ, |l| < 1 / ξ →
      ∫⁻ z, ENNReal.ofReal (Real.exp (l * z)) ∂noise ≤
        ENNReal.ofReal (Real.exp (l ^ 2 * γ ^ 2 / 2)))
    {l : ℝ} (hl : |l| < 1 / ξ) :
    Integrable (fun z : ℝ => Real.exp (l * z)) noise := by
  refine ⟨(by fun_prop : Measurable fun z : ℝ => Real.exp (l * z)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => (Real.exp_pos _).le)]
  exact lt_of_le_of_lt (hse l hl) ENNReal.ofReal_lt_top

/-- Bochner form of the sub-exponential MGF bound. -/
lemma factor_mgf_le {noise : Measure ℝ} {γ ξ : ℝ}
    (hse : ∀ l : ℝ, |l| < 1 / ξ →
      ∫⁻ z, ENNReal.ofReal (Real.exp (l * z)) ∂noise ≤
        ENNReal.ofReal (Real.exp (l ^ 2 * γ ^ 2 / 2)))
    {l : ℝ} (hl : |l| < 1 / ξ) :
    ∫ z, Real.exp (l * z) ∂noise ≤ Real.exp (l ^ 2 * γ ^ 2 / 2) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => (Real.exp_pos _).le)
    (by fun_prop : Measurable fun z : ℝ => Real.exp (l * z)).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (hse l hl)

end ChernoffTailAux

open ChernoffTailAux in
theorem solution
    (N : ℕ) (noise : Measure ℝ) [IsProbabilityMeasure noise]
    (γ ξ : ℝ) (a : Fin N → ℝ) (t s : ℝ)
    (hξ : 0 < ξ) (ha : ∀ i, |a i| ≤ 1)
    (hse : ∀ l : ℝ, |l| < 1 / ξ →
      ∫⁻ z, ENNReal.ofReal (Real.exp (l * z)) ∂noise ≤
        ENNReal.ofReal (Real.exp (l ^ 2 * γ ^ 2 / 2)))
    (ht : 0 < t) (htξ : t < 1 / ξ) :
    (Measure.pi fun _ : Fin N => noise).real {z | s ≤ ∑ i, a i * z i} ≤
      Real.exp (-t * s + t ^ 2 * (∑ i, a i ^ 2) * γ ^ 2 / 2) := by
  set P := Measure.pi fun _ : Fin N => noise with hPdef
  have hfac : ∀ i : Fin N, |t * a i| < 1 / ξ := by
    intro i
    rw [abs_mul, abs_of_pos ht]
    calc t * |a i| ≤ t * 1 := by gcongr; exact ha i
      _ = t := mul_one t
      _ < 1 / ξ := htξ
  -- each factor is integrable over the single-coordinate noise
  have hfacInt : ∀ i : Fin N, Integrable (fun z : ℝ => Real.exp (t * (a i * z))) noise := by
    intro i
    have h := factor_integrable hse (hfac i)
    simpa [mul_assoc] using h
  have hev : ∀ i : Fin N, MeasurePreserving (Function.eval i)
      (Measure.pi fun _ : Fin N => noise) noise :=
    fun i => measurePreserving_eval _ i
  -- ... hence over the product measure, by composition with the coordinate evaluation
  have hint : ∀ i : Fin N,
      Integrable (fun ω : Fin N → ℝ => Real.exp (t * (a i * ω i))) P := by
    intro i
    have h1 : MemLp (fun z : ℝ => Real.exp (t * (a i * z))) 1 noise :=
      memLp_one_iff_integrable.2 (hfacInt i)
    exact memLp_one_iff_integrable.1 (h1.comp_measurePreserving (hev i))
  have hmeas : ∀ i : Fin N, Measurable fun ω : Fin N → ℝ => a i * ω i :=
    fun i => by fun_prop
  have hindep : iIndepFun (fun i (ω : Fin N → ℝ) => a i * ω i) P :=
    iIndepFun_pi fun i => (by fun_prop : Measurable fun z : ℝ => a i * z).aemeasurable
  have hsumInt :
      Integrable (fun ω => Real.exp (t * (∑ i, fun ω' : Fin N → ℝ => a i * ω' i) ω)) P :=
    hindep.integrable_exp_mul_sum hmeas fun i _ => hint i
  -- per-coordinate MGF bound, transported from the noise measure
  have hmgf_i : ∀ i : Fin N,
      mgf (fun ω : Fin N → ℝ => a i * ω i) P t ≤
        Real.exp ((t * a i) ^ 2 * γ ^ 2 / 2) := by
    intro i
    have hxm : AEStronglyMeasurable (fun z : ℝ => Real.exp (t * (a i * z)))
        (P.map (Function.eval i)) :=
      (by fun_prop : Measurable fun z : ℝ => Real.exp (t * (a i * z))).aestronglyMeasurable
    have h1 : mgf (fun ω : Fin N → ℝ => a i * ω i) P t
        = mgf (fun z : ℝ => a i * z) noise t := by
      rw [← (hev i).map_eq]
      exact (mgf_map (hev i).measurable.aemeasurable hxm).symm ▸ rfl
    have h2 : mgf (fun z : ℝ => a i * z) noise t
        = ∫ z, Real.exp ((t * a i) * z) ∂noise := by
      simp only [mgf, mul_assoc]
    rw [h1, h2]
    exact factor_mgf_le hse (hfac i)
  -- assemble via Chernoff and independence
  calc P.real {z | s ≤ ∑ i, a i * z i}
      = P.real {ω | s ≤ (∑ i, fun ω' : Fin N → ℝ => a i * ω' i) ω} := by
        congr 1
        ext ω
        simp [Finset.sum_apply]
    _ ≤ Real.exp (-t * s) * mgf (∑ i, fun ω' : Fin N → ℝ => a i * ω' i) P t :=
        measure_ge_le_exp_mul_mgf s ht.le hsumInt
    _ = Real.exp (-t * s) * ∏ i, mgf (fun ω' : Fin N → ℝ => a i * ω' i) P t := by
        rw [hindep.mgf_sum hmeas]
    _ ≤ Real.exp (-t * s) * ∏ i, Real.exp ((t * a i) ^ 2 * γ ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact Finset.prod_le_prod (fun i _ => mgf_nonneg) fun i _ => hmgf_i i
    _ = Real.exp (-t * s + t ^ 2 * (∑ i, a i ^ 2) * γ ^ 2 / 2) := by
        rw [← Real.exp_sum, ← Real.exp_add]
        have harg : (∑ i, (t * a i) ^ 2 * γ ^ 2 / 2) = t ^ 2 * (∑ i, a i ^ 2) * γ ^ 2 / 2 := by
          rw [← Finset.sum_div, ← Finset.sum_mul]
          have hs : (∑ i, (t * a i) ^ 2) = t ^ 2 * ∑ i, a i ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [hs]
        rw [harg]
