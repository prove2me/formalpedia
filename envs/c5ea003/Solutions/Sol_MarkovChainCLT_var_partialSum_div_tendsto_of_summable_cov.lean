-- Prove2me | solution 1 for MarkovChainCLT.var_partialSum_div_tendsto_of_summable_cov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T06:54:44.698576+00:00
-- url     : https://prove2.me/submissions/22190ef3-0b53-4770-9441-4c54c00d05a1

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

-- Scratch: direct proof of `MarkovChainCLT.var_partialSum_div_tendsto_of_summable_cov`.
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P)) :
    Tendsto (fun n : ℕ => Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)) := by
  have hmap : ∀ k, P.map (Y k) = P.map (Y 0) := by
    intro k
    have h := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (hstat k)
    rw [Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY (n + k)),
      Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY n)] at h
    simpa [Function.comp_def] using h
  have hmemLp : ∀ k, MemLp (Y k) 2 P := by
    intro k
    have h0 : MemLp (id : ℝ → ℝ) 2 (P.map (Y 0)) :=
      (memLp_map_measure_iff (measurable_id.aestronglyMeasurable) (hY 0).aemeasurable).2 hL2
    have hk : MemLp (id : ℝ → ℝ) 2 (P.map (Y k)) := by rw [hmap k]; exact h0
    exact (memLp_map_measure_iff (measurable_id.aestronglyMeasurable) (hY k).aemeasurable).1 hk
  have hmean : ∀ k, ∫ ω, Y k ω ∂P = 0 := by
    intro k
    have h1 : ∫ x, x ∂(P.map (Y k)) = ∫ ω, Y k ω ∂P :=
      integral_map (hY k).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
    have h2 : ∫ x, x ∂(P.map (Y 0)) = ∫ ω, Y 0 ω ∂P :=
      integral_map (hY 0).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
    rw [← h1, hmap k, h2, hcent]
  set c : ℕ → ℝ := fun k => ∫ ω, Y 0 ω * Y k ω ∂P with hc
  have hc_def : ∀ k, c k = ∫ ω, Y 0 ω * Y k ω ∂P := fun k => rfl
  have hpair : ∀ i d : ℕ, ∫ ω, Y i ω * Y (i + d) ω ∂P = c d := by
    intro i d
    have hgm : Measurable (fun f : ℕ → ℝ => f 0 * f d) :=
      (measurable_pi_apply 0).mul (measurable_pi_apply d)
    have hmeasi : Measurable (fun ω n => Y (n + i) ω) :=
      measurable_pi_lambda _ fun n => hY (n + i)
    have hmeas0 : Measurable (fun ω n => Y n ω) :=
      measurable_pi_lambda _ fun n => hY n
    have e1 : ∫ f, f 0 * f d ∂(Measure.map (fun ω n => Y (n + i) ω) P)
        = ∫ ω, Y i ω * Y (i + d) ω ∂P := by
      rw [integral_map hmeasi.aemeasurable hgm.aestronglyMeasurable]
      apply integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show Y (0 + i) ω * Y (d + i) ω = Y i ω * Y (i + d) ω
      rw [Nat.zero_add, Nat.add_comm d i]
    have e2 : ∫ f, f 0 * f d ∂(Measure.map (fun ω n => Y n ω) P)
        = ∫ ω, Y 0 ω * Y d ω ∂P := by
      rw [integral_map hmeas0.aemeasurable hgm.aestronglyMeasurable]
    rw [hc_def d]
    rw [hstat i] at e1
    rw [e2] at e1
    exact e1.symm
  have hcov : ∀ i j : ℕ, i ≤ j → cov[Y i, Y j; P] = c (j - i) := by
    intro i j hij
    have hji : j = i + (j - i) := (Nat.add_sub_cancel' hij).symm
    rw [covariance]
    simp only [hmean i, hmean j, sub_zero]
    conv_lhs => rw [hji]
    exact hpair i (j - i)
  have hF : ∀ n : ℕ, (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cov[Y i, Y j; P])
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcol : ∑ i ∈ Finset.range n, cov[Y i, Y n; P]
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e1 : ∀ i ∈ Finset.range n, cov[Y i, Y n; P] = c ((n - 1 - i) + 1) := by
          intro i hi
          rw [Finset.mem_range] at hi
          have hiN : i ≤ n := Nat.le_of_lt hi
          have h := hcov i n hiN
          have hni : n - i = (n - 1 - i) + 1 := by omega
          rw [hni] at h
          exact h
        rw [Finset.sum_congr rfl e1]
        exact Finset.sum_range_reflect (fun j => c (j + 1)) n
      have hrow : ∑ j ∈ Finset.range n, cov[Y n, Y j; P]
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e : ∀ j ∈ Finset.range n, cov[Y n, Y j; P] = cov[Y j, Y n; P] :=
          fun j _ => covariance_comm (Y n) (Y j)
        rw [Finset.sum_congr rfl e]
        exact hcol
      have hdiag : cov[Y n, Y n; P] = c 0 := by
        have h := hcov n n le_rfl
        simpa using h
      rw [Finset.sum_range_succ]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib, ih, hcol, hrow, hdiag]
      push_cast
      ring
  have hV : ∀ n : ℕ, Var[∑ i ∈ Finset.range n, Y i; P]
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cov[Y i, Y j; P] :=
    fun n => variance_sum' (fun i _ => hmemLp i)
  have hVD : ∀ n : ℕ, Var[∑ i ∈ Finset.range n, Y i; P]
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) :=
    fun n => (hV n).trans (hF n)
  have hsig : seqAsymptoticVariance P Y = c 0 + 2 * ∑' k, c (k + 1) := by
    have hc0 : c 0 = ∫ ω, Y 0 ω * Y 0 ω ∂P := rfl
    have hsq : (∫ ω, (Y 0 ω) ^ 2 ∂P) = ∫ ω, Y 0 ω * Y 0 ω ∂P := by
      congr 1; ext ω; rw [pow_two]
    show (∫ ω, (Y 0 ω) ^ 2 ∂P) + 2 * ∑' k : ℕ, ∫ ω, Y 0 ω * Y (k + 1) ω ∂P = _
    rw [hsq, hc0]
  rw [hsig]
  have hD : Tendsto (fun m => ∑ k ∈ Finset.range m, c (k + 1)) atTop
      (𝓝 (∑' k, c (k + 1))) :=
    hsum.hasSum.tendsto_sum_nat
  have hces := hD.cesaro
  have hadd : Tendsto
      (fun n : ℕ => c 0 + 2 * ((n⁻¹ : ℝ) * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1)))
      atTop (𝓝 (c 0 + 2 * ∑' k, c (k + 1))) :=
    tendsto_const_nhds.add (hces.const_mul 2)
  refine Filter.Tendsto.congr' ?h hadd
  filter_upwards [eventually_ge_atTop 1] with n hn
  show c 0 + 2 * ((n⁻¹ : ℝ) * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1))
    = Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ)
  rw [hVD n]
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
