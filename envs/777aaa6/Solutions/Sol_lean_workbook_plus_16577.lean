-- Prove2me | solution 1 for lean_workbook_plus_16577
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:27:29.664545+00:00
-- url     : https://prove2.me/submissions/0600f473-1853-41b2-b654-b058cf9e7e50

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

noncomputable def sparseDenominatorSpike (n : ℕ) : ℝ := by
  classical
  exact if n ∈ Set.range (fun k : ℕ => 2 ^ k) then 1 / ((n : ℝ) + 1) else 0

noncomputable def sparseDenominatorSequence (n : ℕ) : ℝ := by
  classical
  exact if n ∈ Set.range (fun k : ℕ => 2 ^ k) then 1 / ((n : ℝ) + 1)
    else 1 / ((n : ℝ) + 1) ^ 2

theorem sparse_denominator_spike_summable : Summable sparseDenominatorSpike := by
  have hinj : Function.Injective (fun k : ℕ => 2 ^ k) :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
  apply (hinj.summable_iff (f := sparseDenominatorSpike) (by
    intro n hn
    simp [sparseDenominatorSpike, hn])).mp
  have hg : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  apply hg.of_nonneg_of_le
  · intro k
    simp only [Function.comp_apply, sparseDenominatorSpike,
      if_pos (Set.mem_range_self k)]
    positivity
  · intro k
    simp only [Function.comp_apply, sparseDenominatorSpike,
      if_pos (Set.mem_range_self k)]
    have hp : 0 < (2 : ℝ) ^ k := by positivity
    have hle : 1 / ((2 : ℝ) ^ k + 1) ≤ 1 / (2 : ℝ) ^ k :=
      one_div_le_one_div_of_le hp (by linarith)
    simpa only [Nat.cast_pow, Nat.cast_ofNat, div_pow, one_pow] using hle

theorem sparse_denominator_base_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem sparse_denominator_positive (n : ℕ) : 0 < sparseDenominatorSequence n := by
  unfold sparseDenominatorSequence
  split_ifs <;> positivity

theorem sparse_denominator_below_reciprocal (n : ℕ) (hn : 0 < n) :
    sparseDenominatorSequence n < 1 / (n : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold sparseDenominatorSequence
  split_ifs
  · exact one_div_lt_one_div_of_lt hn' (by linarith)
  · apply one_div_lt_one_div_of_lt hn'
    nlinarith [sq_nonneg (n : ℝ)]

theorem sparse_denominator_summable : Summable sparseDenominatorSequence := by
  apply (sparse_denominator_base_summable.add sparse_denominator_spike_summable).of_nonneg_of_le
  · intro n
    exact (sparse_denominator_positive n).le
  · intro n
    dsimp [sparseDenominatorSequence, sparseDenominatorSpike]
    split_ifs <;> linarith [show 0 ≤ 1 / ((n : ℝ) + 1) ^ 2 by positivity]

theorem sparse_denominator_at_power (k : ℕ) :
    sparseDenominatorSequence (2 ^ k) = 1 / ((2 : ℝ) ^ k + 1) := by
  simp only [sparseDenominatorSequence, if_pos (Set.mem_range_self k),
    Nat.cast_pow, Nat.cast_ofNat]

theorem sparse_denominator_transformed_at_power (k : ℕ) :
    sparseDenominatorSequence (2 ^ k) /
      (1 - (2 ^ k : ℕ) * sparseDenominatorSequence (2 ^ k)) = 1 := by
  rw [sparse_denominator_at_power]
  push_cast
  have hd : 0 < (2 : ℝ) ^ k + 1 := by positivity
  have heq : 1 - (2 : ℝ) ^ k * (1 / ((2 : ℝ) ^ k + 1)) =
      1 / ((2 : ℝ) ^ k + 1) := by
    field_simp
    ring
  rw [heq]
  exact div_self (ne_of_gt (one_div_pos.mpr hd))

theorem sparse_denominator_transformed_not_summable :
    ¬ Summable (fun n : ℕ => sparseDenominatorSequence n /
      (1 - (n : ℝ) * sparseDenominatorSequence n)) := by
  intro h
  have hinj : Function.Injective (fun k : ℕ => 2 ^ k) :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
  have hsub := h.comp_injective hinj
  have hone : Summable (fun _ : ℕ => (1 : ℝ)) := hsub.congr
    (fun k => sparse_denominator_transformed_at_power k)
  have hzero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hone.tendsto_atTop_zero
  norm_num at hzero

theorem sparse_denominator_positive_index_counterexample :
    ∃ x : ℕ → ℝ, (∀ n, 0 < n → 0 < x n ∧ x n < 1 / (n : ℝ)) ∧
      Summable x ∧ ¬ Summable (fun n => x n / (1 - (n : ℝ) * x n)) := by
  exact ⟨sparseDenominatorSequence,
    fun n hn => ⟨sparse_denominator_positive n, sparse_denominator_below_reciprocal n hn⟩,
    sparse_denominator_summable, sparse_denominator_transformed_not_summable⟩

theorem summable_denominator_transform_of_uniform_gap (x : ℕ → ℝ)
    (hx : ∀ n, 0 ≤ x n) (hs : Summable x) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ n : ℕ, δ ≤ 1 - (n : ℝ) * x n) :
    Summable (fun n => x n / (1 - (n : ℝ) * x n)) := by
  apply (hs.div_const δ).of_nonneg_of_le
  · intro n
    exact div_nonneg (hx n) (hδ.le.trans (hgap n))
  · intro n
    exact div_le_div_of_nonneg_left (hx n) hδ (hgap n)

theorem sparse_denominator_source_counterexample :
    ∃ x : ℕ → ℝ,
      (∀ n : ℕ, 0 < x (n + 1) ∧ x (n + 1) < 1 / ((n : ℝ) + 1)) ∧
      Summable (fun n => x (n + 1)) ∧
      ¬ Summable (fun n : ℕ => x (n + 1) / (1 - ((n : ℝ) + 1) * x (n + 1))) := by
  refine ⟨sparseDenominatorSequence, ?_, ?_, ?_⟩
  · intro n
    refine ⟨sparse_denominator_positive (n + 1), ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using
      sparse_denominator_below_reciprocal (n + 1) (Nat.succ_pos n)
  · exact (summable_nat_add_iff 1).mpr sparse_denominator_summable
  · intro h
    apply sparse_denominator_transformed_not_summable
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using h

theorem solution (x : ℕ → ℝ) (hx : ∀ n, 0 < x n ∧ x n < 1 / n)
    (h : Summable x) : Summable (fun n => x n / (1 - n * x n)) := by
  have hzero := hx 0
  norm_num at hzero
  exact False.elim (lt_asymm hzero.1 hzero.2)

#print axioms sparseDenominatorSpike
#print axioms sparseDenominatorSequence
#print axioms sparse_denominator_spike_summable
#print axioms sparse_denominator_base_summable
#print axioms sparse_denominator_positive
#print axioms sparse_denominator_below_reciprocal
#print axioms sparse_denominator_summable
#print axioms sparse_denominator_at_power
#print axioms sparse_denominator_transformed_at_power
#print axioms sparse_denominator_transformed_not_summable
#print axioms sparse_denominator_positive_index_counterexample
#print axioms summable_denominator_transform_of_uniform_gap
#print axioms sparse_denominator_source_counterexample
#print axioms solution
