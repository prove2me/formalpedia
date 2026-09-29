-- Prove2me | solution 2 for bernoulli_event_failure_probability_decomposes_by_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T03:41:36.433988+00:00
-- url     : https://prove2.me/submissions/7407bd9c-7595-4757-b044-6fdefbccf4f2

import Definitions.Def_matrix_completion_fixed_cardinality
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
open MatrixCompletion
open scoped Classical BigOperators
open Finset

namespace SolAux

variable {n₁ n₂ : ℕ}

/-- Total Bernoulli mass is 1. -/
theorem total_mass (p : ℝ) :
    ∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω = 1 := by
  unfold bernoulliObservationWeight
  have := Fintype.sum_pow_mul_eq_add_pow (Fin n₁ × Fin n₂) p (1 - p)
  rw [this]
  simp

/-- Number of size-`k` subsets satisfying / not satisfying Event. -/
theorem card_layer_le (m : ℕ) (Event : Finset (Fin n₁ × Fin n₂) → Prop)
    (hm : m ≤ n₁ * n₂) :
    ((Finset.powersetCard m (Finset.univ : Finset (Fin n₁ × Fin n₂))).filter Event).card
      ≤ (n₁ * n₂).choose m := by
  calc _ ≤ (Finset.powersetCard m (Finset.univ : Finset (Fin n₁ × Fin n₂))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = (Fintype.card (Fin n₁ × Fin n₂)).choose m := by
        rw [Finset.card_powersetCard, Finset.card_univ]
    _ = (n₁ * n₂).choose m := by rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

end SolAux

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    1 - bernoulliEventProb p Event =
      ∑ k ∈ Finset.range (n₁ * n₂ + 1),
        binomialCardinalityProb (n₁ * n₂) k p *
          (1 - fixedCardinalityEventProb k Event) := by
  intro hp0 hp1
  classical
  set M := n₁ * n₂ with hM
  -- abbreviation
  -- 1 - bern = ∑_Ω w(Ω) - ∑_Ω [Event Ω] w(Ω) = ∑_Ω [¬Event Ω] w(Ω)
  have hbern : bernoulliEventProb p Event
      = ∑ Ω : Finset (Fin n₁ × Fin n₂),
          (if Event Ω then bernoulliObservationWeight p Ω else 0) := rfl
  have hcompl : 1 - bernoulliEventProb p Event
      = ∑ Ω : Finset (Fin n₁ × Fin n₂),
          (if Event Ω then 0 else bernoulliObservationWeight p Ω) := by
    rw [hbern, ← SolAux.total_mass (n₁ := n₁) (n₂ := n₂) p, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro Ω _
    by_cases h : Event Ω <;> simp [h]
  rw [hcompl]
  -- group by cardinality
  have hMcard : (Finset.univ : Finset (Fin n₁ × Fin n₂)).card = M := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hgroup : ∑ Ω : Finset (Fin n₁ × Fin n₂),
        (if Event Ω then 0 else bernoulliObservationWeight p Ω)
      = ∑ k ∈ Finset.range (M + 1),
          ∑ Ω ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n₁ × Fin n₂)),
            (if Event Ω then 0 else bernoulliObservationWeight p Ω) := by
    have h1 : ∑ Ω : Finset (Fin n₁ × Fin n₂),
          (if Event Ω then 0 else bernoulliObservationWeight p Ω)
        = ∑ Ω ∈ (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset,
            (if Event Ω then 0 else bernoulliObservationWeight p Ω) := by
      rw [Finset.powerset_univ]
    rw [h1, Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion, hMcard]
  rw [hgroup]
  -- per-layer identity
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  set L := Finset.powersetCard k (Finset.univ : Finset (Fin n₁ × Fin n₂)) with hL
  set c : ℝ := p ^ k * (1 - p) ^ (M - k) with hc
  -- weight is constant c on L
  have hw : ∀ Ω ∈ L, bernoulliObservationWeight p Ω = c := by
    intro Ω hΩ
    rw [hL, Finset.mem_powersetCard] at hΩ
    rw [bernoulliObservationWeight, hΩ.2, hc, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  -- LHS = c * #(filter ¬Event L)
  have hLHS : ∑ Ω ∈ L, (if Event Ω then 0 else bernoulliObservationWeight p Ω)
      = c * ((L.filter (fun Ω => ¬ Event Ω)).card : ℝ) := by
    have h1 : ∑ Ω ∈ L, (if Event Ω then 0 else bernoulliObservationWeight p Ω)
        = ∑ Ω ∈ L, (if Event Ω then (0:ℝ) else c) := by
      apply Finset.sum_congr rfl
      intro Ω hΩ
      by_cases h : Event Ω
      · simp [h]
      · simp [h, hw Ω hΩ]
    rw [h1]
    have h2 : ∑ Ω ∈ L, (if Event Ω then (0:ℝ) else c)
        = ∑ Ω ∈ L.filter (fun Ω => ¬ Event Ω), c := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro Ω _
      by_cases h : Event Ω <;> simp [h]
    rw [h2, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- card identity: #(filter ¬Event L) = C(M,k) - #(filter Event L)
  have hLcard : L.card = (M).choose k := by
    rw [hL, Finset.card_powersetCard, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  have hcardsplit : (L.filter (fun Ω => ¬ Event Ω)).card
      = L.card - (L.filter Event).card := by
    rw [Finset.filter_not, Finset.card_sdiff]
    congr 1
    rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
  -- RHS computation
  have hCpos : 0 < (M.choose k) := Nat.choose_pos hk
  have hCposR : (0:ℝ) < (M.choose k : ℝ) := by exact_mod_cast hCpos
  rw [hLHS, hcardsplit, hLcard]
  rw [binomialCardinalityProb, fixedCardinalityEventProb]
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  -- now both sides over ℝ; let A = #(filter Event L), C = C(M,k)
  set A : ℕ := (L.filter Event).card with hA
  have hAle : A ≤ M.choose k := by
    rw [hA, ← hLcard]; exact Finset.card_le_card (Finset.filter_subset _ _)
  have hsubR : ((M.choose k - A : ℕ) : ℝ) = (M.choose k : ℝ) - (A : ℝ) := by
    rw [Nat.cast_sub hAle]
  rw [hsubR, hc]
  have hCne : ((n₁ * n₂).choose k : ℝ) ≠ 0 := by
    rw [← hM]; exact ne_of_gt hCposR
  field_simp
  ring
