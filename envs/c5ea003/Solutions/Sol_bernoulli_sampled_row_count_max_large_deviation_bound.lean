-- Prove2me | solution 1 for bernoulli_sampled_row_count_max_large_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-21T21:01:54.407992+00:00
-- url     : https://prove2.me/submissions/2c96ee34-d7a5-40a3-a718-fe2e18c6d3de

import Definitions.Def_matrix_completion_sampled_counts
import Mathlib.Analysis.Complex.ExponentialBounds
open MatrixCompletion
open Finset
open scoped Classical BigOperators

-- card of the fiber over a fixed first coordinate
lemma fiber_card {n₁ n₂ : ℕ} (i : Fin n₁) :
    (univ.filter (fun c : Fin n₁ × Fin n₂ => c.1 = i)).card = n₂ := by
  have h : (univ.filter (fun c : Fin n₁ × Fin n₂ => c.1 = i))
        = ({i} : Finset (Fin n₁)) ×ˢ (univ : Finset (Fin n₂)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
  rw [h, Finset.card_product]
  simp

-- the cell↔row card bridge via image
lemma bridge_card {n₁ n₂ : ℕ} (i : Fin n₁) (Ω : Finset (Fin n₁ × Fin n₂)) :
    (Ω.filter (fun c => c.1 = i)).card
      = (univ.filter (fun j : Fin n₂ => (i, j) ∈ Ω)).card := by
  have himg : (univ.filter (fun j : Fin n₂ => (i, j) ∈ Ω)).image (fun j => (i, j))
        = Ω.filter (fun c => c.1 = i) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨hj, rfl⟩
    · rintro ⟨hcΩ, hci⟩
      refine ⟨c.2, ?_, ?_⟩
      · have hc : (i, c.2) = c := by rw [← hci]
        rw [hc]; exact hcΩ
      · rw [← hci]
  rw [← himg]
  exact Finset.card_image_of_injective _
    (by intro a b hab; simpa using hab : Function.Injective (fun j : Fin n₂ => (i, j)))

-- per-row MGF factorization
lemma mgf_row {n₁ n₂ : ℕ} (p : ℝ) (i : Fin n₁) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        Real.exp (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
          * (p ^ Ω.card *
              (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card)))
      = (1 - p + p * Real.exp 1) ^ n₂ := by
  -- per-summand identity
  have hsummand : ∀ Ω : Finset (Fin n₁ × Fin n₂),
      Real.exp (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
          * (p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
        = (∏ c ∈ Ω, (if c.1 = i then p * Real.exp 1 else p))
            * ∏ _c ∈ univ \ Ω, (1 - p) := by
    intro Ω
    -- compute ∏ c∈Ω, ite
    have e1 : (∏ c ∈ Ω, (if c.1 = i then p * Real.exp 1 else p))
        = p ^ Ω.card * Real.exp (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0) := by
      have hsplit : (∏ c ∈ Ω, (if c.1 = i then p * Real.exp 1 else p))
          = (∏ _c ∈ Ω, p) * (∏ c ∈ Ω, (if c.1 = i then Real.exp 1 else 1)) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro c _
        by_cases hc : c.1 = i <;> simp [hc]
      rw [hsplit, Finset.prod_const]
      congr 1
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
        bridge_card i Ω, Finset.sum_boole]
      rw [← Real.exp_nat_mul, mul_one]
    rw [Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, e1]
    ring
  -- factorization of the product over cells into a sum over subsets
  have factor : (∏ c : Fin n₁ × Fin n₂,
        ((if c.1 = i then p * Real.exp 1 else p) + (1 - p)))
      = ∑ Ω : Finset (Fin n₁ × Fin n₂),
          (∏ c ∈ Ω, (if c.1 = i then p * Real.exp 1 else p))
            * ∏ _c ∈ univ \ Ω, (1 - p) := by
    rw [Finset.prod_add, Finset.powerset_univ]
  -- simplification of the cell product
  have simp_prod : (∏ c : Fin n₁ × Fin n₂,
        ((if c.1 = i then p * Real.exp 1 else p) + (1 - p)))
      = (1 - p + p * Real.exp 1) ^ n₂ := by
    rw [show (∏ c : Fin n₁ × Fin n₂,
              ((if c.1 = i then p * Real.exp 1 else p) + (1 - p)))
          = ∏ c : Fin n₁ × Fin n₂, (if c.1 = i then (1 - p + p * Real.exp 1) else 1) from ?_]
    · rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, fiber_card i]
    · apply Finset.prod_congr rfl
      intro c _
      by_cases hc : c.1 = i
      · simp only [if_pos hc]; ring
      · simp only [if_neg hc]; ring
  calc (∑ Ω : Finset (Fin n₁ × Fin n₂),
          Real.exp (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
            * (p ^ Ω.card *
                (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card)))
        = ∑ Ω : Finset (Fin n₁ × Fin n₂),
            (∏ c ∈ Ω, (if c.1 = i then p * Real.exp 1 else p))
              * ∏ _c ∈ univ \ Ω, (1 - p) := Finset.sum_congr rfl (fun Ω _ => hsummand Ω)
      _ = ∏ c : Fin n₁ × Fin n₂,
            ((if c.1 = i then p * Real.exp 1 else p) + (1 - p)) := factor.symm
      _ = (1 - p + p * Real.exp 1) ^ n₂ := simp_prod

-- per-row Markov / Chernoff step
lemma per_row_chernoff {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n₁) (t : ℝ) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if t < (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ Real.exp (-t) * (1 - p + p * Real.exp 1) ^ n₂ := by
  have hstep : (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if t < (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ ∑ Ω : Finset (Fin n₁ × Fin n₂),
          Real.exp (-t) *
            (Real.exp (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
              * (p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))) := by
    apply Finset.sum_le_sum
    intro Ω _
    set R := (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0) with hR
    set W := p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) with hW
    have hWnn : 0 ≤ W := mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    by_cases h : t < R
    · rw [if_pos h]
      have h1 : (1 : ℝ) ≤ Real.exp (-t) * Real.exp R := by
        rw [← Real.exp_add, Real.one_le_exp_iff]; linarith
      calc W = 1 * W := (one_mul _).symm
        _ ≤ (Real.exp (-t) * Real.exp R) * W := mul_le_mul_of_nonneg_right h1 hWnn
        _ = Real.exp (-t) * (Real.exp R * W) := by ring
    · rw [if_neg h]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hWnn)
  refine le_trans hstep (le_of_eq ?_)
  rw [← Finset.mul_sum, mgf_row p i]

-- union bound over rows
lemma union_row {n₁ n₂ : ℕ} (hn1 : 0 < n₁) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if t < (⨆ i : Fin n₁, ∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ ∑ i : Fin n₁, ∑ Ω : Finset (Fin n₁ × Fin n₂),
          if t < (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
          then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0 := by
  have hterm : (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if t < (⨆ i : Fin n₁, ∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ ∑ Ω : Finset (Fin n₁ × Fin n₂), ∑ i : Fin n₁,
          if t < (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
          then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0 := by
    apply Finset.sum_le_sum
    intro Ω _
    haveI : Nonempty (Fin n₁) := ⟨⟨0, hn1⟩⟩
    set W := p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) with hW
    have hWnn : 0 ≤ W := mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    have hnn : ∀ k : Fin n₁,
        0 ≤ (if t < (∑ j : Fin n₂, if (k, j) ∈ Ω then (1 : ℝ) else 0) then W else 0) := by
      intro k
      by_cases hh : t < (∑ j : Fin n₂, if (k, j) ∈ Ω then (1 : ℝ) else 0)
      · rw [if_pos hh]; exact hWnn
      · rw [if_neg hh]
    by_cases h : t < (⨆ i : Fin n₁, ∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
    · rw [if_pos h]
      obtain ⟨i₀, hi₀⟩ := exists_lt_of_lt_ciSup h
      calc W = (if t < (∑ j : Fin n₂, if (i₀, j) ∈ Ω then (1 : ℝ) else 0) then W else 0) := by
              rw [if_pos hi₀]
        _ ≤ ∑ i : Fin n₁,
              (if t < (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0) then W else 0) :=
            Finset.single_le_sum (fun i _ => hnn i) (mem_univ i₀)
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun i _ => hnn i)
  exact le_trans hterm (le_of_eq Finset.sum_comm)

theorem solution :
    ∃ Cdev : ℝ, 0 < Cdev ∧
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (lambda : ℝ), 2 ≤ lambda →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              lambda *
                  (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (↑(max n₁ n₂))) <
                sampledRowCountMax Omega) ≤
          (↑(max n₁ n₂)) *
            Real.exp
              (-(lambda *
                  (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (↑(max n₁ n₂)))) / Cdev) := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have he3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  refine ⟨2 / (3 - Real.exp 1), by positivity, ?_⟩
  intro n₁ n₂ m hn1 hn2 hm lambda hlam
  have hN0 : 0 < ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  set p := ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) with hp_def
  have hp0 : 0 ≤ p := by rw [hp_def]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one hN0]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at this ⊢; linarith
  set K := max n₁ n₂ with hK_def
  set t := lambda * (p * (K : ℝ)) with ht_def
  have hKn2 : (n₂ : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.le_max_right n₁ n₂
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    have : 1 ≤ K := le_max_of_le_left hn1
    exact_mod_cast this
  have hpK0 : 0 ≤ p * (K : ℝ) := mul_nonneg hp0 (by linarith)
  have ht0 : 0 ≤ t := by rw [ht_def]; nlinarith [hpK0, hlam]
  -- p * n₂ ≤ t / 2
  have hpn2 : p * (n₂ : ℝ) ≤ t / 2 := by
    have h1 : p * (n₂ : ℝ) ≤ p * (K : ℝ) := mul_le_mul_of_nonneg_left hKn2 hp0
    have h2 : 2 * (p * (K : ℝ)) ≤ lambda * (p * (K : ℝ)) :=
      mul_le_mul_of_nonneg_right hlam hpK0
    rw [ht_def]; linarith
  -- per-row bound
  have hrow : ∀ i : Fin n₁,
      (∑ Ω : Finset (Fin n₁ × Fin n₂),
          if t < (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
          then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
        ≤ Real.exp (-t / (2 / (3 - Real.exp 1))) := by
    intro i
    refine le_trans (per_row_chernoff p hp0 hp1 i t) ?_
    have heq : 1 - p + p * Real.exp 1 = p * (Real.exp 1 - 1) + 1 := by ring
    have hbase_nn : 0 ≤ 1 - p + p * Real.exp 1 := by
      rw [heq]; have := mul_nonneg hp0 (by linarith : (0:ℝ) ≤ Real.exp 1 - 1); linarith
    have hbase_le : 1 - p + p * Real.exp 1 ≤ Real.exp (p * (Real.exp 1 - 1)) := by
      rw [heq]; exact Real.add_one_le_exp _
    have hpow : (1 - p + p * Real.exp 1) ^ n₂
        ≤ Real.exp ((n₂ : ℝ) * (p * (Real.exp 1 - 1))) := by
      calc (1 - p + p * Real.exp 1) ^ n₂
          ≤ (Real.exp (p * (Real.exp 1 - 1))) ^ n₂ := pow_le_pow_left₀ hbase_nn hbase_le n₂
        _ = Real.exp ((n₂ : ℝ) * (p * (Real.exp 1 - 1))) := (Real.exp_nat_mul _ _).symm
    have hstep2 : Real.exp (-t) * (1 - p + p * Real.exp 1) ^ n₂
        ≤ Real.exp (-t) * Real.exp ((n₂ : ℝ) * (p * (Real.exp 1 - 1))) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    refine le_trans hstep2 ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hCval : -t / (2 / (3 - Real.exp 1)) = -t * (3 - Real.exp 1) / 2 := by
      rw [div_div_eq_mul_div]
    rw [hCval]
    have hmul : (Real.exp 1 - 1) * (p * (n₂ : ℝ)) ≤ (Real.exp 1 - 1) * (t / 2) :=
      mul_le_mul_of_nonneg_left hpn2 (by linarith)
    nlinarith [hmul, ht0, he1, he3]
  -- assemble
  show bernoulliEventProb p (fun Ω => t < sampledRowCountMax Ω)
      ≤ (K : ℝ) * Real.exp (-t / (2 / (3 - Real.exp 1)))
  have hunfold : bernoulliEventProb p (fun Ω => t < sampledRowCountMax Ω)
      = ∑ Ω : Finset (Fin n₁ × Fin n₂),
          if t < (⨆ i : Fin n₁, ∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
          then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0 := rfl
  rw [hunfold]
  calc (∑ Ω : Finset (Fin n₁ × Fin n₂),
          if t < (⨆ i : Fin n₁, ∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
          then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
        ≤ ∑ i : Fin n₁, ∑ Ω : Finset (Fin n₁ × Fin n₂),
            if t < (∑ j : Fin n₂, if (i, j) ∈ Ω then (1 : ℝ) else 0)
            then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0 :=
          union_row hn1 p hp0 hp1 t
      _ ≤ ∑ _i : Fin n₁, Real.exp (-t / (2 / (3 - Real.exp 1))) :=
          Finset.sum_le_sum (fun i _ => hrow i)
      _ = (n₁ : ℝ) * Real.exp (-t / (2 / (3 - Real.exp 1))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (K : ℝ) * Real.exp (-t / (2 / (3 - Real.exp 1))) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact_mod_cast Nat.le_max_left n₁ n₂
