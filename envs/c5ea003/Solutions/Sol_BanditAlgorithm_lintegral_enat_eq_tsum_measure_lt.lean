-- Prove2me | solution 1 for BanditAlgorithm.lintegral_enat_eq_tsum_measure_lt
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T19:31:13.546476+00:00
-- url     : https://prove2.me/submissions/fc7d786b-4ec3-4d00-a837-7b00d2609bc8

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability


/-!
# The expectation of an `ℕ∞`-valued random variable as a tail sum

`E[τ] = ∑_{n ≥ 0} P(τ > n)`.

This is the identity every sample-complexity bound for a stopping rule runs on:
Garivier–Kaufmann's Proposition 13 (and L&S §33.2.2) bound `E[τ_δ]` by exhibiting
a round `N` after which the rule fires with overwhelming probability, and then
summing the tail.  The `ℕ∞` version is the one that is needed, because a bandit
stopping time is allowed to be `⊤`; the identity then correctly returns `⊤` when
`P(τ = ∞) > 0`.

The file also records the two consequences that are actually used:

* `lintegral_enat_le_add_tsum` — `E[τ] ≤ N + ∑_{n ≥ N} P(τ > n)`, the form in
  which one plugs in a tail estimate valid only from some round on;
* `lintegral_enat_ne_top_of_tsum_ne_top` — a summable tail forces `E[τ] < ∞`.
-/

open MeasureTheory ENNReal Set

namespace BanditAlgorithm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Pointwise layer-cake: `n ↦ 1{n < m}` sums to `m`. -/
theorem tsum_indicator_lt_enat (m : ℕ∞) :
    (∑' n : ℕ, if (n : ℕ∞) < m then (1 : ℝ≥0∞) else 0) = (m : ℝ≥0∞) := by
  classical
  rcases eq_or_ne m ⊤ with rfl | hm
  · have h1 : (fun n : ℕ ↦ if (n : ℕ∞) < (⊤ : ℕ∞) then (1 : ℝ≥0∞) else 0)
        = fun _ : ℕ ↦ (1 : ℝ≥0∞) := by
      funext n
      rw [if_pos (ENat.coe_lt_top n)]
    rw [h1, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
    simp
  · obtain ⟨j, rfl⟩ := ENat.ne_top_iff_exists.mp hm
    have hsupp : ∀ n ∉ Finset.range j, (if (n : ℕ∞) < ((j : ℕ) : ℕ∞) then (1 : ℝ≥0∞) else 0) = 0 := by
      intro n hn
      rw [if_neg]
      intro hlt
      exact hn (Finset.mem_range.mpr (by exact_mod_cast hlt))
    rw [tsum_eq_sum hsupp]
    have hin : ∀ n ∈ Finset.range j,
        (if (n : ℕ∞) < ((j : ℕ) : ℕ∞) then (1 : ℝ≥0∞) else 0) = 1 := by
      intro n hn
      rw [if_pos]
      exact_mod_cast Finset.mem_range.mp hn
    rw [Finset.sum_congr rfl hin]
    simp

/-- **The tail-sum formula.**  For an `ℕ∞`-valued measurable `τ`,
`E[τ] = ∑_{n ≥ 0} P(τ > n)`. -/
theorem lintegral_enat_eq_tsum_measure_lt {τ : Ω → ℕ∞} (hτ : Measurable τ) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {ω | (n : ℕ∞) < τ ω} := by
  classical
  have hmeas : ∀ n : ℕ, MeasurableSet {ω | (n : ℕ∞) < τ ω} := fun n ↦
    hτ (t := Set.Ioi (n : ℕ∞)) MeasurableSet.of_discrete
  have hpt : (fun ω ↦ (τ ω : ℝ≥0∞))
      = fun ω ↦ ∑' n : ℕ, if (n : ℕ∞) < τ ω then (1 : ℝ≥0∞) else 0 := by
    funext ω
    exact (tsum_indicator_lt_enat (τ ω)).symm
  rw [hpt, MeasureTheory.lintegral_tsum
    (fun n ↦ (Measurable.ite (hmeas n) measurable_const measurable_const).aemeasurable)]
  refine tsum_congr fun n ↦ ?_
  have : (fun ω ↦ if (n : ℕ∞) < τ ω then (1 : ℝ≥0∞) else 0)
      = Set.indicator {ω | (n : ℕ∞) < τ ω} (fun _ ↦ (1 : ℝ≥0∞)) := by
    funext ω; by_cases h : (n : ℕ∞) < τ ω <;> simp [h, Set.indicator]
  rw [this]
  simp [lintegral_indicator (hmeas n)]

/-- The shift equivalence `ℕ ≃ {n | N ≤ n}`. -/
def shiftEquiv (N : ℕ) : ℕ ≃ {n : ℕ // N ≤ n} where
  toFun n := ⟨n + N, Nat.le_add_left N n⟩
  invFun m := m.1 - N
  left_inv n := by simp
  right_inv m := by
    ext
    simpa using Nat.sub_add_cancel m.2

/-- Splitting an `ℝ≥0∞`-valued series at index `N`. -/
theorem tsum_eq_sum_range_add_tsum_shift (f : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑' n : ℕ, f n = (∑ n ∈ Finset.range N, f n) + ∑' n : ℕ, f (n + N) := by
  classical
  set s : Set ℕ := {n : ℕ | n < N} with hs
  have hsplit : (∑' x : s, f x) + ∑' x : (sᶜ : Set ℕ), f x = ∑' n : ℕ, f n :=
    ENNReal.summable.tsum_add_tsum_compl ENNReal.summable
  have h1 : (∑' x : s, f x) = ∑ n ∈ Finset.range N, f n := by
    have hset : s = (↑(Finset.range N) : Set ℕ) := by
      ext n; simp [hs]
    rw [hset, ← Finset.tsum_subtype]
    rfl
  have hcompl : (sᶜ : Set ℕ) = {n : ℕ | N ≤ n} := by
    ext n; simp [hs]
  have h2 : (∑' x : (sᶜ : Set ℕ), f x) = ∑' n : ℕ, f (n + N) := by
    rw [hcompl]
    exact ((shiftEquiv N).tsum_eq fun x ↦ f x).symm
  rw [← hsplit, h1, h2]

/-- `E[τ] ≤ N + ∑_{n ≥ N} P(τ > n)`: the tail estimate only has to hold from some
round on. -/
theorem lintegral_enat_le_add_tsum {τ : Ω → ℕ∞} (hτ : Measurable τ)
    [IsProbabilityMeasure μ] (N : ℕ) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≤ (N : ℝ≥0∞) + ∑' n : ℕ, μ {ω | ((n + N : ℕ) : ℕ∞) < τ ω} := by
  classical
  set f : ℕ → ℝ≥0∞ := fun n ↦ μ {ω | (n : ℕ∞) < τ ω} with hf
  have hsum : ∑ n ∈ Finset.range N, f n ≤ (N : ℝ≥0∞) := by
    calc ∑ n ∈ Finset.range N, f n ≤ ∑ _n ∈ Finset.range N, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun n _ ↦ prob_le_one
      _ = (N : ℝ≥0∞) := by simp
  calc ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, f n := lintegral_enat_eq_tsum_measure_lt hτ
    _ = (∑ n ∈ Finset.range N, f n) + ∑' n : ℕ, f (n + N) :=
        tsum_eq_sum_range_add_tsum_shift f N
    _ ≤ (N : ℝ≥0∞) + ∑' n : ℕ, f (n + N) := add_le_add_left hsum _

/-- A summable tail bound forces a finite expectation. -/
theorem lintegral_enat_ne_top_of_le {τ : Ω → ℕ∞} (hτ : Measurable τ) {g : ℕ → ℝ≥0∞}
    (hg : ∀ n : ℕ, μ {ω | (n : ℕ∞) < τ ω} ≤ g n) (hgs : (∑' n : ℕ, g n) ≠ ⊤) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≠ ⊤ := by
  rw [lintegral_enat_eq_tsum_measure_lt hτ]
  exact ne_top_of_le_ne_top hgs (ENNReal.tsum_le_tsum hg)

/-- Monotone comparison: a stochastically smaller stopping time has a smaller
expectation. -/
theorem lintegral_enat_mono {τ σ : Ω → ℕ∞} (h : ∀ ω, τ ω ≤ σ ω) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≤ ∫⁻ ω, (σ ω : ℝ≥0∞) ∂μ :=
  lintegral_mono fun ω ↦ ENat.toENNReal_mono (h ω)

/-- If `τ` is bounded by `N` everywhere then `E[τ] ≤ N`. -/
theorem lintegral_enat_le_of_le_const {τ : Ω → ℕ∞} [IsProbabilityMeasure μ] {N : ℕ}
    (h : ∀ ω, τ ω ≤ (N : ℕ∞)) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≤ (N : ℝ≥0∞) := by
  calc ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≤ ∫⁻ _ω, ((N : ℕ∞) : ℝ≥0∞) ∂μ :=
        lintegral_mono fun ω ↦ ENat.toENNReal_mono (h ω)
    _ = (N : ℝ≥0∞) := by simp

end BanditAlgorithm


theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {τ : Ω → ℕ∞} (hτ : Measurable τ) :
    ∫⁻ ω, (τ ω : ENNReal) ∂μ = ∑' n : ℕ, μ {ω | (n : ℕ∞) < τ ω} :=
  BanditAlgorithm.lintegral_enat_eq_tsum_measure_lt hτ
