-- Prove2me | solution 1 for MovingSofa.ForMathlib.alternating_series_bracket_of_antitone_shift
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-11-04T03:00:09.968167+00:00
-- url     : https://prove2.me/submissions/5544c8ec-a6f8-4cdb-b0e6-c8f212bc4d8a

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
open scoped BigOperators


/-- Leibniz bracketing for an alternating series whose term magnitudes are antitone only
from index `2 * N` onwards: the limit lies between the partial sums of `2 * N` and of
`2 * N + 1` terms. -/
theorem solution {f : ℕ → ℝ} {l : ℝ} (N : ℕ)
    (hfl : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
      Filter.atTop (nhds l))
    (hfa : Antitone fun n ↦ f (2 * N + n)) :
    (∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * f i) ≤ l ∧
      l ≤ ∑ i ∈ Finset.range (2 * N + 1), (-1 : ℝ) ^ i * f i := by
  set S := ∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * f i with hS
  have key : ∀ n : ℕ, (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f (2 * N + i))
      = (∑ i ∈ Finset.range (2 * N + n), (-1 : ℝ) ^ i * f i) - S := by
    intro n
    rw [hS, Finset.sum_range_add]
    simp [pow_add, pow_mul]
  have hshift : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (2 * N + n), (-1 : ℝ) ^ i * f i)
      Filter.atTop (nhds l) := by
    have h := hfl.comp (Filter.tendsto_add_atTop_nat (2 * N))
    simpa [Function.comp_def, Nat.add_comm] using h
  have htend : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f (2 * N + i))
      Filter.atTop (nhds (l - S)) := by
    simp only [key]
    exact hshift.sub_const S
  have hlow := Antitone.alternating_series_le_tendsto htend hfa 0
  have hhigh := Antitone.tendsto_le_alternating_series htend hfa 0
  simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, Nat.zero_add,
    Finset.sum_range_one, pow_zero, one_mul, Nat.add_zero] at hlow hhigh
  refine ⟨by linarith, ?_⟩
  rw [Finset.sum_range_succ, ← hS, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  linarith
