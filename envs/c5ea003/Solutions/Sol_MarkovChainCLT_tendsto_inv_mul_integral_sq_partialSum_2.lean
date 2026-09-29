-- Prove2me | solution 2 for MarkovChainCLT.tendsto_inv_mul_integral_sq_partialSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T07:56:08.186811+00:00
-- url     : https://prove2.me/submissions/caee9733-8b09-4483-a8a8-6f74e9476aeb

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) atTop
      (𝓝 (seqAsymptoticVariance P Y)) := by
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
  have hprod : ∀ i j : ℕ, Integrable (fun ω => Y i ω * Y j ω) P :=
    fun i j => (hmemLp i).integrable_mul (hmemLp j)
  have hexp : ∀ n : ℕ, (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P)
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∫ ω, Y i ω * Y j ω ∂P := by
    intro n
    have hsq : (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2)
        = (fun ω => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Y i ω * Y j ω) := by
      funext ω
      rw [pow_two, Finset.sum_mul_sum]
    rw [hsq, integral_finsetSum (Finset.range n)
      (fun i _ => integrable_finsetSum (Finset.range n) (fun j _ => hprod i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_finsetSum (Finset.range n) (fun j _ => hprod i j)
  have hF : ∀ n : ℕ, (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∫ ω, Y i ω * Y j ω ∂P)
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcol : ∑ i ∈ Finset.range n, (∫ ω, Y i ω * Y n ω ∂P)
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e1 : ∀ i ∈ Finset.range n, (∫ ω, Y i ω * Y n ω ∂P) = c ((n - 1 - i) + 1) := by
          intro i hi
          rw [Finset.mem_range] at hi
          have hiN : i ≤ n := Nat.le_of_lt hi
          have h1 : i + (n - i) = n := Nat.add_sub_cancel' hiN
          have h := hpair i (n - i)
          have hni : n - i = (n - 1 - i) + 1 := by omega
          rw [h1] at h
          rw [hni] at h
          exact h
        rw [Finset.sum_congr rfl e1]
        exact Finset.sum_range_reflect (fun j => c (j + 1)) n
      have hrow : ∑ j ∈ Finset.range n, (∫ ω, Y n ω * Y j ω ∂P)
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e : ∀ j ∈ Finset.range n, (∫ ω, Y n ω * Y j ω ∂P)
            = (∫ ω, Y j ω * Y n ω ∂P) :=
          fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
        rw [Finset.sum_congr rfl e]
        exact hcol
      have hdiag : (∫ ω, Y n ω * Y n ω ∂P) = c 0 := by
        have h := hpair n 0
        simpa using h
      rw [Finset.sum_range_succ]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib, ih, hcol, hrow, hdiag]
      push_cast
      ring
  have hE : ∀ n : ℕ, (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P)
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) :=
    fun n => (hexp n).trans (hF n)
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
    = (n : ℝ)⁻¹ * ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
  rw [hE n]
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
