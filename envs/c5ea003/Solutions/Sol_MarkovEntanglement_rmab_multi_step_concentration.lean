-- Prove2me | solution 1 for MarkovEntanglement.rmab_multi_step_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T00:33:59.669821+00:00
-- url     : https://prove2.me/submissions/0e399345-2c72-4bc7-971d-a94a7b24b6f0

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace ME9

set_option linter.unusedSectionVars false

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Products supported on one or two indices -/

theorem prod_one {N : ℕ} {β : Type*} [CommMonoid β] (i : Fin N) (G : Fin N → β)
    (hG : ∀ j, j ≠ i → G j = 1) : ∏ j, G j = G i :=
  Finset.prod_eq_single i (fun b _ hb => hG b hb) (fun h => absurd (Finset.mem_univ i) h)

theorem prod_two {N : ℕ} {β : Type*} [CommMonoid β] {i k : Fin N} (hik : i ≠ k)
    (G : Fin N → β) (hG : ∀ j, j ≠ i → j ≠ k → G j = 1) : ∏ j, G j = G i * G k := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  refine Finset.prod_eq_single k (fun b hb hbk => hG b (Finset.ne_of_mem_erase hb) hbk) ?_
  intro h
  exact absurd (Finset.mem_erase.2 ⟨Ne.symm hik, Finset.mem_univ k⟩) h

/-! ### Expectations under a product measure -/

/-- Summing a product of one-coordinate functions over all joint states factorises. -/
theorem sum_prod_eq {N : ℕ} (f : Fin N → S → ℝ) :
    ∑ s' : Fin N → S, ∏ j, f j (s' j) = ∏ j, ∑ y, f j y := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- Under a product measure, the expectation of a product of one-coordinate functions is the
product of the expectations: the coordinates are independent. -/
theorem prod_expect {N : ℕ} (κ : Fin N → S → ℝ) (G : Fin N → S → ℝ) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * ∏ j, G j (s' j) = ∏ j, ∑ y, κ j y * G j y := by
  rw [← sum_prod_eq (fun j y => κ j y * G j y)]
  exact Finset.sum_congr rfl fun s' _ => Finset.prod_mul_distrib.symm

theorem expect_const {N : ℕ} (κ : Fin N → S → ℝ) (hκ : ∀ j, ∑ y, κ j y = 1) :
    ∑ s' : Fin N → S, ∏ j, κ j (s' j) = 1 := by
  rw [sum_prod_eq]
  simp [hκ]

theorem expect_single {N : ℕ} (κ : Fin N → S → ℝ) (hκ : ∀ j, ∑ y, κ j y = 1)
    (i : Fin N) (g : S → ℝ) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * g (s' i) = ∑ y, κ i y * g y := by
  classical
  have h1 : ∀ s' : Fin N → S, (∏ j, (if j = i then g (s' j) else (1:ℝ))) = g (s' i) := by
    intro s'
    rw [prod_one i _ (fun j hj => by simp only [if_neg hj]), if_pos rfl]
  calc ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * g (s' i)
      = ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * ∏ j, (if j = i then g (s' j) else (1:ℝ)) :=
        Finset.sum_congr rfl fun s' _ => by rw [h1 s']
    _ = ∏ j, ∑ y, κ j y * (if j = i then g y else (1:ℝ)) :=
        prod_expect κ (fun j y => if j = i then g y else (1:ℝ))
    _ = ∑ y, κ i y * g y := by
        rw [prod_one i _ (fun j hj => by simp only [if_neg hj, mul_one]; exact hκ j)]
        simp

theorem expect_pair {N : ℕ} (κ : Fin N → S → ℝ) (hκ : ∀ j, ∑ y, κ j y = 1)
    {i k : Fin N} (hik : i ≠ k) (g h : S → ℝ) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * (g (s' i) * h (s' k))
      = (∑ y, κ i y * g y) * (∑ y, κ k y * h y) := by
  classical
  have h1 : ∀ s' : Fin N → S,
      (∏ j, (if j = i then g (s' j) else if j = k then h (s' j) else (1:ℝ)))
        = g (s' i) * h (s' k) := by
    intro s'
    rw [prod_two hik _ (fun j hj hk => by simp only [if_neg hj, if_neg hk])]
    simp [Ne.symm hik]
  calc ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * (g (s' i) * h (s' k))
      = ∑ s' : Fin N → S, (∏ j, κ j (s' j))
          * ∏ j, (if j = i then g (s' j) else if j = k then h (s' j) else (1:ℝ)) :=
        Finset.sum_congr rfl fun s' _ => by rw [h1 s']
    _ = ∏ j, ∑ y, κ j y * (if j = i then g y else if j = k then h y else (1:ℝ)) :=
        prod_expect κ (fun j y => if j = i then g y else if j = k then h y else (1:ℝ))
    _ = (∑ y, κ i y * g y) * (∑ y, κ k y * h y) := by
        rw [prod_two hik _ (fun j hj hk => by
          simp only [if_neg hj, if_neg hk, mul_one]; exact hκ j)]
        simp [Ne.symm hik]

/-! ### The conditional one-step estimate -/

theorem sum_ind {N : ℕ} (s' : Fin N → S) (y : S) :
    (stateCount s' y : ℝ) = ∑ j, (if s' j = y then (1:ℝ) else 0) := by
  unfold stateCount
  rw [Finset.card_filter]
  push_cast
  rfl

theorem cond_bound {N : ℕ} (hN : 0 < N) (κ : Fin N → S → ℝ)
    (hκnn : ∀ j y, 0 ≤ κ j y) (hκ1 : ∀ j, ∑ y, κ j y = 1)
    (φ : S → ℝ) (hφ : ∀ y, ∑ j, κ j y = (N : ℝ) * φ y) :
    ∑ s' : Fin N → S, (∏ j, κ j (s' j)) *
        (∑ y, |(stateCount s' y : ℝ) / (N : ℝ) - φ y|)
      ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
  classical
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hνnn : ∀ s' : Fin N → S, 0 ≤ ∏ j, κ j (s' j) :=
    fun s' => Finset.prod_nonneg fun j _ => hκnn j (s' j)
  have hνsum : ∑ s' : Fin N → S, ∏ j, κ j (s' j) = 1 := expect_const κ hκ1
  -- the centred indicators
  have hZW : ∀ (y : S) (s' : Fin N → S),
      (N:ℝ) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)
        = ∑ j, ((if s' j = y then (1:ℝ) else 0) - κ j y) := by
    intro y s'
    rw [Finset.sum_sub_distrib, ← sum_ind s' y, hφ y]
    field_simp
  -- first moments vanish
  have hE1 : ∀ (j : Fin N) (y : S),
      ∑ s' : Fin N → S, (∏ l, κ l (s' l)) * ((if s' j = y then (1:ℝ) else 0) - κ j y) = 0 := by
    intro j y
    rw [expect_single κ hκ1 j (fun z => (if z = y then (1:ℝ) else 0) - κ j y)]
    have : ∀ z : S, κ j z * ((if z = y then (1:ℝ) else 0) - κ j y)
        = (if z = y then κ j z else 0) - κ j z * κ j y := by
      intro z
      by_cases h : z = y <;> simp [h] <;> ring
    rw [Finset.sum_congr rfl (fun z _ => this z), Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ y (fun z => κ j z), ← Finset.sum_mul, hκ1 j]
    simp
  -- second moments
  have hE2diag : ∀ (j : Fin N) (y : S),
      ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
        (((if s' j = y then (1:ℝ) else 0) - κ j y) * ((if s' j = y then (1:ℝ) else 0) - κ j y))
        = κ j y - κ j y * κ j y := by
    intro j y
    rw [expect_single κ hκ1 j
      (fun z => ((if z = y then (1:ℝ) else 0) - κ j y) * ((if z = y then (1:ℝ) else 0) - κ j y))]
    have hpt : ∀ z : S, κ j z * (((if z = y then (1:ℝ) else 0) - κ j y)
        * ((if z = y then (1:ℝ) else 0) - κ j y))
        = (1 - 2 * κ j y) * (if z = y then κ j z else 0) + κ j z * (κ j y * κ j y) := by
      intro z
      by_cases h : z = y <;> simp [h] <;> ring
    rw [Finset.sum_congr rfl (fun z _ => hpt z), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ y (fun z => κ j z), ← Finset.sum_mul, hκ1 j]
    simp only [Finset.mem_univ, if_true]
    ring
  have hE2off : ∀ (j k : Fin N) (y : S), j ≠ k →
      ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
        (((if s' j = y then (1:ℝ) else 0) - κ j y) * ((if s' k = y then (1:ℝ) else 0) - κ k y))
        = 0 := by
    intro j k y hjk
    rw [expect_pair κ hκ1 hjk (fun z => (if z = y then (1:ℝ) else 0) - κ j y)
      (fun z => (if z = y then (1:ℝ) else 0) - κ k y)]
    have h1 : ∑ z, κ j z * ((if z = y then (1:ℝ) else 0) - κ j y) = 0 := by
      have := hE1 j y
      rwa [expect_single κ hκ1 j (fun z => (if z = y then (1:ℝ) else 0) - κ j y)] at this
    rw [h1, zero_mul]
  -- the second moment of the deviation
  have hkey : ∀ y : S, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
      ((N:ℝ) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)) ^ 2
      = ∑ j, (κ j y - κ j y * κ j y) := by
    intro y
    have hexp : ∀ s' : Fin N → S,
        ((N:ℝ) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)) ^ 2
          = ∑ j, ∑ k, (((if s' j = y then (1:ℝ) else 0) - κ j y)
              * ((if s' k = y then (1:ℝ) else 0) - κ k y)) := by
      intro s'
      rw [hZW y s', sq, Finset.sum_mul_sum]
    calc ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
            ((N:ℝ) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)) ^ 2
        = ∑ s' : Fin N → S, ∑ j, ∑ k, (∏ l, κ l (s' l)) *
            (((if s' j = y then (1:ℝ) else 0) - κ j y)
              * ((if s' k = y then (1:ℝ) else 0) - κ k y)) := by
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [hexp s', Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
      _ = ∑ j, ∑ k, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
            (((if s' j = y then (1:ℝ) else 0) - κ j y)
              * ((if s' k = y then (1:ℝ) else 0) - κ k y)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ j, (κ j y - κ j y * κ j y) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single j (fun k _ hk => hE2off j k y (Ne.symm hk))
            (fun h => absurd (Finset.mem_univ j) h)]
          exact hE2diag j y
  have hvar : ∀ y : S, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
      ((stateCount s' y : ℝ) / (N:ℝ) - φ y) ^ 2
      = (∑ j, (κ j y - κ j y * κ j y)) / (N:ℝ) ^ 2 := by
    intro y
    rw [← hkey y, Finset.sum_div]
    refine Finset.sum_congr rfl fun s' _ => ?_
    field_simp
  have hvarle : ∑ y, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
      ((stateCount s' y : ℝ) / (N:ℝ) - φ y) ^ 2 ≤ 1 / (N:ℝ) := by
    have hdiv : ∀ a b c : ℝ, a ≤ b → 0 < c → a / c ≤ b / c := by
      intro a b c hab hc
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hab (le_of_lt (inv_pos.2 hc))
    calc ∑ y, ∑ s' : Fin N → S, (∏ l, κ l (s' l)) *
            ((stateCount s' y : ℝ) / (N:ℝ) - φ y) ^ 2
        = ∑ y, (∑ j, (κ j y - κ j y * κ j y)) / (N:ℝ) ^ 2 :=
          Finset.sum_congr rfl fun y _ => hvar y
      _ ≤ ∑ y, (∑ j, κ j y) / (N:ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun y _ => hdiv _ _ _ ?_ (by positivity)
          refine Finset.sum_le_sum fun j _ => ?_
          nlinarith [hκnn j y]
      _ = (∑ y, ∑ j, κ j y) / (N:ℝ) ^ 2 := by rw [Finset.sum_div]
      _ = (N:ℝ) / (N:ℝ) ^ 2 := by
          rw [Finset.sum_comm]
          simp [hκ1]
      _ = 1 / (N:ℝ) := by
          field_simp
  -- Cauchy-Schwarz
  have hterm : ∀ p : S × (Fin N → S),
      Real.sqrt (∏ l, κ l (p.2 l)) *
        Real.sqrt ((∏ l, κ l (p.2 l)) * ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2)
      = (∏ l, κ l (p.2 l)) * |(stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1| := by
    intro p
    rw [Real.sqrt_mul (hνnn p.2), ← mul_assoc, Real.mul_self_sqrt (hνnn p.2),
      Real.sqrt_sq_eq_abs]
  have hCS := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (S × (Fin N → S)))
      (f := fun p : S × (Fin N → S) => ∏ l, κ l (p.2 l))
      (g := fun p : S × (Fin N → S) =>
        (∏ l, κ l (p.2 l)) * ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2)
      (fun p => hνnn p.2) (fun p => mul_nonneg (hνnn p.2) (sq_nonneg _))
  have hf : ∑ p : S × (Fin N → S), (∏ l, κ l (p.2 l)) = (Fintype.card S : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp [hνsum]
  have hgle : ∑ p : S × (Fin N → S),
      (∏ l, κ l (p.2 l)) * ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2 ≤ 1 / (N:ℝ) := by
    rw [Fintype.sum_prod_type]
    exact hvarle
  have hL : ∑ p : S × (Fin N → S),
      (∏ l, κ l (p.2 l)) * |(stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1|
      = ∑ s' : Fin N → S, (∏ j, κ j (s' j)) *
          (∑ y, |(stateCount s' y : ℝ) / (N : ℝ) - φ y|) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    simp only [Finset.mul_sum]
  calc ∑ s' : Fin N → S, (∏ j, κ j (s' j)) *
          (∑ y, |(stateCount s' y : ℝ) / (N : ℝ) - φ y|)
      = ∑ p : S × (Fin N → S), Real.sqrt (∏ l, κ l (p.2 l)) *
          Real.sqrt ((∏ l, κ l (p.2 l)) *
            ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2) := by
        rw [← hL]
        exact (Finset.sum_congr rfl fun p _ => hterm p).symm
    _ ≤ Real.sqrt (∑ p : S × (Fin N → S), (∏ l, κ l (p.2 l))) *
          Real.sqrt (∑ p : S × (Fin N → S),
            (∏ l, κ l (p.2 l)) * ((stateCount p.2 p.1 : ℝ) / (N:ℝ) - φ p.1) ^ 2) := hCS
    _ ≤ Real.sqrt (Fintype.card S : ℝ) * Real.sqrt (1 / (N:ℝ)) := by
        rw [hf]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgle) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        ring

/-! ### Index policies activate a deterministic number of agents in each local state -/

/-- The number of agents sitting in state `x` that the joint action `a` activates. -/
def cnt {N : ℕ} (st : Fin N → S) (a : Fin N → Bool) (x : S) : ℕ :=
  (Finset.univ.filter fun i => st i = x ∧ a i = true).card

theorem sum_cnt {N : ℕ} (st : Fin N → S) (a : Fin N → Bool) :
    ∑ x, cnt st a x = (Finset.univ.filter fun i => a i = true).card := by
  classical
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := st) (t := (Finset.univ : Finset S))
    (fun i _ => Finset.mem_univ (st i))]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem count_mul_prob {N : ℕ} (ν : S → ℝ) (M : ℕ) (st : Fin N → S) (x : S) :
    (stateCount st x : ℝ) * indexActivationProb ν M st x = (activateCount ν M st x : ℝ) := by
  unfold indexActivationProb activateCount
  split_ifs with h
  · rw [h]; simp
  · have hne : ((stateCount st x : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 h
    field_simp

theorem expect_cnt {N : ℕ} (ν : S → ℝ) (M : ℕ) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν M π) (st : Fin N → S) (x : S) :
    ∑ a : Fin N → Bool, π st a * (cnt st a x : ℝ) = (activateCount ν M st x : ℝ) := by
  classical
  have hcnt : ∀ a : Fin N → Bool, (cnt st a x : ℝ)
      = ∑ i, (if st i = x then (if a i = true then (1:ℝ) else 0) else 0) := by
    intro a
    unfold cnt
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : st i = x <;> by_cases h2 : a i = true <;> simp [h1, h2]
  calc ∑ a : Fin N → Bool, π st a * (cnt st a x : ℝ)
      = ∑ a : Fin N → Bool, ∑ i,
          (if st i = x then (if a i = true then π st a else 0) else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hcnt a, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h1 : st i = x <;> by_cases h2 : a i = true <;> simp [h1, h2]
    _ = ∑ i, ∑ a : Fin N → Bool,
          (if st i = x then (if a i = true then π st a else 0) else 0) := Finset.sum_comm
    _ = ∑ i, (if st i = x then indexActivationProb ν M st x else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h1 : st i = x
        · simp only [if_pos h1]
          rw [← h1]
          exact hπ.2.2 st i
        · simp [h1]
    _ = (activateCount ν M st x : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        exact count_mul_prob ν M st x

/-- An agent whose activation probability is one is activated by every action in the support. -/
theorem support_true {N : ℕ} (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hnn : ∀ st a, 0 ≤ π st a) (hsum : ∀ st, ∑ a, π st a = 1)
    (st : Fin N → S) (i : Fin N)
    (h : ∑ a : Fin N → Bool, (if a i = true then π st a else 0) = 1)
    (a : Fin N → Bool) (ha : π st a ≠ 0) : a i = true := by
  classical
  by_contra hcon
  have hzero : ∑ b : Fin N → Bool, (if b i = true then 0 else π st b) = 0 := by
    have hsplit : ∀ b : Fin N → Bool,
        (if b i = true then π st b else 0) + (if b i = true then 0 else π st b) = π st b := by
      intro b
      by_cases hb : b i = true <;> simp [hb]
    have := Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hsplit b)
    rw [Finset.sum_add_distrib, h, hsum st] at this
    linarith
  have hnn' : ∀ b ∈ (Finset.univ : Finset (Fin N → Bool)),
      0 ≤ (if b i = true then 0 else π st b) := by
    intro b _
    by_cases hb : b i = true <;> simp [hb, hnn st b]
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn').1 hzero a (Finset.mem_univ a)
  rw [if_neg hcon] at this
  exact ha this

/-- An agent whose activation probability is zero is never activated in the support. -/
theorem support_false {N : ℕ} (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hnn : ∀ st a, 0 ≤ π st a) (st : Fin N → S) (i : Fin N)
    (h : ∑ a : Fin N → Bool, (if a i = true then π st a else 0) = 0)
    (a : Fin N → Bool) (ha : π st a ≠ 0) : a i = false := by
  classical
  by_contra hcon
  have htrue : a i = true := by simpa using hcon
  have hnn' : ∀ b ∈ (Finset.univ : Finset (Fin N → Bool)),
      0 ≤ (if b i = true then π st b else 0) := by
    intro b _
    by_cases hb : b i = true <;> simp [hb, hnn st b]
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn').1 h a (Finset.mem_univ a)
  rw [if_pos htrue] at this
  exact ha this

/-- The activated counts add up to the budget. -/
theorem sum_activateCount {N : ℕ} (ν : S → ℝ) (M : ℕ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπ : IsIndexPolicy ν M π) (st : Fin N → S) :
    ∑ x, activateCount ν M st x = M := by
  classical
  have hR : ((∑ x, activateCount ν M st x : ℕ) : ℝ) = (M : ℝ) := by
    push_cast
    calc ∑ x, (activateCount ν M st x : ℝ)
        = ∑ x, ∑ a : Fin N → Bool, π st a * (cnt st a x : ℝ) :=
          (Finset.sum_congr rfl fun x _ => expect_cnt ν M π hπ st x).symm
      _ = ∑ a : Fin N → Bool, ∑ x, π st a * (cnt st a x : ℝ) := Finset.sum_comm
      _ = ∑ a : Fin N → Bool, π st a * ((Finset.univ.filter fun i => a i = true).card : ℝ) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.mul_sum]
          congr 1
          rw [← Nat.cast_sum, sum_cnt]
      _ = ∑ a : Fin N → Bool, π st a * (M : ℝ) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases ha : π st a = 0
          · rw [ha]; ring
          · rw [hπ.2.1 st a ha]
      _ = (M : ℝ) := by rw [← Finset.sum_mul, hπ.1.2 st, one_mul]
  exact_mod_cast hR

/-- If `x` has strictly lower priority than `y`, the count above `y` together with `y` itself
is part of the count above `x`. -/
theorem hpc_add_le {N : ℕ} (ν : S → ℝ) (st : Fin N → S) {x y : S} (hxy : ν x < ν y) :
    higherPriorityCount ν st y + stateCount st y ≤ higherPriorityCount ν st x := by
  classical
  unfold higherPriorityCount
  have hy : y ∉ Finset.univ.filter (fun z => ν y < ν z) := by simp
  rw [add_comm, ← Finset.sum_insert hy]
  refine Finset.sum_le_sum_of_subset ?_
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  rcases hz with rfl | hz
  · exact hxy
  · exact hxy.trans hz

/-- At most one local state is served fractionally. -/
theorem frac_unique {N : ℕ} (ν : S → ℝ) (M : ℕ) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν M π) (st : Fin N → S) {x y : S}
    (hx : 0 < activateCount ν M st x ∧ activateCount ν M st x < stateCount st x)
    (hy : 0 < activateCount ν M st y ∧ activateCount ν M st y < stateCount st y) : x = y := by
  classical
  by_contra hne
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hax : activateCount ν M st x
      = min (stateCount st x) (M - higherPriorityCount ν st x) := rfl
  have hay : activateCount ν M st y
      = min (stateCount st y) (M - higherPriorityCount ν st y) := rfl
  have hcx1 : activateCount ν M st x = M - higherPriorityCount ν st x := by omega
  have hcx2 : higherPriorityCount ν st x < M := by omega
  have hcy1 : activateCount ν M st y = M - higherPriorityCount ν st y := by omega
  have hcy2 : higherPriorityCount ν st y < M := by omega
  rcases lt_trichotomy (ν x) (ν y) with hlt | heq | hgt
  · have h := hpc_add_le ν st hlt
    omega
  · have hfil : (Finset.univ.filter fun z => ν x < ν z)
        = (Finset.univ.filter fun z => ν y < ν z) := by
      ext z
      simp [heq]
    have hhx : higherPriorityCount ν st x = higherPriorityCount ν st y := by
      unfold higherPriorityCount
      rw [hfil]
    have hA : ∀ z ∈ Finset.univ.filter (fun z => ν x < ν z),
        activateCount ν M st z = stateCount st z := by
      intro z hz
      have hzx : ν x < ν z := (Finset.mem_filter.1 hz).2
      have h := hpc_add_le ν st hzx
      have haz : activateCount ν M st z
          = min (stateCount st z) (M - higherPriorityCount ν st z) := rfl
      omega
    have hsumA : ∑ z ∈ Finset.univ.filter (fun z => ν x < ν z), activateCount ν M st z
        = higherPriorityCount ν st x := by
      rw [Finset.sum_congr rfl hA]
      rfl
    have hxA : x ∉ Finset.univ.filter (fun z => ν x < ν z) := by simp
    have hyA : y ∉ Finset.univ.filter (fun z => ν x < ν z) := by simp [heq]
    have hxins : x ∉ insert y (Finset.univ.filter fun z => ν x < ν z) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hne, hxA⟩
    have hbig : ∑ z ∈ insert x (insert y (Finset.univ.filter fun z => ν x < ν z)),
        activateCount ν M st z ≤ ∑ z, activateCount ν M st z :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_insert hxins, Finset.sum_insert hyA, hsumA,
      sum_activateCount ν M π hπ st] at hbig
    omega
  · have h := hpc_add_le ν st hgt
    omega

/-- Under an index policy the number of activated agents in each local state is the same for
every action in the policy's support: it is `activateCount`. -/
theorem cnt_eq {N : ℕ} (ν : S → ℝ) (M : ℕ) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν M π) (st : Fin N → S) (a : Fin N → Bool) (ha : π st a ≠ 0) (x : S) :
    cnt st a x = activateCount ν M st x := by
  classical
  have hdet : ∀ z : S, ¬(0 < activateCount ν M st z ∧ activateCount ν M st z < stateCount st z) →
      cnt st a z = activateCount ν M st z := by
    intro z hz
    have haz : activateCount ν M st z
        = min (stateCount st z) (M - higherPriorityCount ν st z) := rfl
    have hle : activateCount ν M st z ≤ stateCount st z := by omega
    rcases Nat.eq_zero_or_pos (stateCount st z) with hn | hn
    · have hc : activateCount ν M st z = 0 := by omega
      have hz0 : cnt st a z = 0 := by
        unfold cnt
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have hmem : i ∈ Finset.univ.filter (fun i => st i = z) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hi.1
        have hn' : (Finset.univ.filter fun i => st i = z) = ∅ := by
          rw [← Finset.card_eq_zero]
          exact hn
        rw [hn'] at hmem
        simp at hmem
      omega
    · have hq := hπ.2.2 st
      rcases Nat.lt_or_ge (activateCount ν M st z) (stateCount st z) with hlt | hge
      · have hc0 : activateCount ν M st z = 0 := by omega
        have hprob : indexActivationProb ν M st z = 0 := by
          unfold indexActivationProb
          rw [if_neg (by omega), hc0]
          simp
        have hall : ∀ i, st i = z → a i = false := by
          intro i hi
          refine support_false π hπ.1.1 st i ?_ a ha
          have hqi := hq i
          rw [hi, hprob] at hqi
          exact hqi
        have hz0 : cnt st a z = 0 := by
          unfold cnt
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [hall i hi.1] at hi
          simp at hi
        omega
      · have hcn : activateCount ν M st z = stateCount st z := le_antisymm hle hge
        have hprob : indexActivationProb ν M st z = 1 := by
          unfold indexActivationProb
          rw [if_neg (by omega), hcn]
          field_simp
        have hall : ∀ i, st i = z → a i = true := by
          intro i hi
          refine support_true π hπ.1.1 hπ.1.2 st i ?_ a ha
          have hqi := hq i
          rw [hi, hprob] at hqi
          exact hqi
        have hzn : cnt st a z = stateCount st z := by
          unfold cnt stateCount
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.1, fun h => ⟨h, hall i h⟩⟩
        omega
  by_cases hx : 0 < activateCount ν M st x ∧ activateCount ν M st x < stateCount st x
  · have hother : ∀ z ∈ Finset.univ.erase x, cnt st a z = activateCount ν M st z := by
      intro z hz
      refine hdet z ?_
      intro hfz
      exact (Finset.ne_of_mem_erase hz) (frac_unique ν M π hπ st hfz hx)
    have h1 : ∑ z, cnt st a z = ∑ z, activateCount ν M st z := by
      rw [sum_cnt, hπ.2.1 st a ha, sum_activateCount ν M π hπ st]
    have h2 : cnt st a x + ∑ z ∈ Finset.univ.erase x, cnt st a z
        = activateCount ν M st x + ∑ z ∈ Finset.univ.erase x, activateCount ν M st z := by
      rw [Finset.add_sum_erase _ (fun z => cnt st a z) (Finset.mem_univ x),
        Finset.add_sum_erase _ (fun z => activateCount ν M st z) (Finset.mem_univ x)]
      exact h1
    have h3 : ∑ z ∈ Finset.univ.erase x, cnt st a z
        = ∑ z ∈ Finset.univ.erase x, activateCount ν M st z := Finset.sum_congr rfl hother
    omega
  · exact hdet x hx

/-! ### Assembling the one-step bound -/

theorem fiber_sum {N : ℕ} (st : Fin N → S) (F : S → ℝ) :
    ∑ j, F (st j) = ∑ x, (stateCount st x : ℝ) * F x := by
  classical
  have h1 : ∀ j : Fin N, F (st j) = ∑ x, (if st j = x then F x else 0) := by
    intro j
    rw [Finset.sum_ite_eq Finset.univ (st j) F]
    simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem fiber_sum_act {N : ℕ} (st : Fin N → S) (a : Fin N → Bool) (F : S → ℝ) :
    ∑ j, (if a j = true then F (st j) else 0) = ∑ x, (cnt st a x : ℝ) * F x := by
  classical
  have h1 : ∀ j : Fin N, (if a j = true then F (st j) else 0)
      = ∑ x, (if st j = x ∧ a j = true then F x else 0) := by
    intro j
    by_cases h : a j = true
    · have hx : ∀ x : S, (if st j = x ∧ a j = true then F x else 0)
          = (if st j = x then F x else 0) := by
        intro x
        by_cases hxx : st j = x <;> simp [hxx, h]
      rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_ite_eq Finset.univ (st j) F]
      simp [h]
    · have hx : ∀ x : S, (if st j = x ∧ a j = true then F x else 0) = 0 := by
        intro x; simp [h]
      rw [Finset.sum_congr rfl (fun x _ => hx x)]
      simp [h]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem hpm_eq {N : ℕ} (ν : S → ℝ) (st : Fin N → S) (x : S) :
    higherPriorityMass ν (configuration st) x = (higherPriorityCount ν st x : ℝ) / (N : ℝ) := by
  unfold higherPriorityMass higherPriorityCount configuration
  rw [Nat.cast_sum, Finset.sum_div]

theorem activateFraction_eq {N : ℕ} (ν : S → ℝ) (M : ℕ) (hN : 0 < N) (st : Fin N → S) (x : S) :
    activateFraction ν ((M : ℝ) / (N : ℝ)) (configuration st) x
      = (activateCount ν M st x : ℝ) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold activateFraction
  rw [hpm_eq, div_sub_div_same]
  unfold configuration activateCount
  rcases le_total (higherPriorityCount ν st x) M with hle | hge
  · have h1 : (0 : ℝ) ≤ ((M : ℝ) - (higherPriorityCount ν st x : ℝ)) / (N : ℝ) := by
      have : ((higherPriorityCount ν st x : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hle
      positivity
    rw [max_eq_right h1, min_div_div_right hNpos.le]
    congr 1
    rw [Nat.cast_min, Nat.cast_sub hle]
  · have h0 : M - higherPriorityCount ν st x = 0 := Nat.sub_eq_zero_of_le hge
    have h1 : ((M : ℝ) - (higherPriorityCount ν st x : ℝ)) / (N : ℝ) ≤ 0 := by
      have : (M : ℝ) ≤ (higherPriorityCount ν st x : ℝ) := by exact_mod_cast hge
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    rw [max_eq_left h1, h0]
    simp
    positivity

theorem kernel_sum_eq {N : ℕ} (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (M : ℕ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπ : IsIndexPolicy ν M π)
    (st : Fin N → S) (a : Fin N → Bool) (ha : π st a ≠ 0) (y : S) :
    ∑ j, rmabKernel P0 P1 (st j) (a j) y
      = (N : ℝ) * meanFieldMap P0 P1 ν ((M : ℝ) / (N : ℝ)) (configuration st) y := by
  classical
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hsplit : ∀ j : Fin N, rmabKernel P0 P1 (st j) (a j) y
      = P0 (st j) y + (if a j = true then (P1 (st j) y - P0 (st j) y) else 0) := by
    intro j
    unfold rmabKernel
    by_cases h : a j = true <;> simp [h]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    fiber_sum st (fun x => P0 x y), fiber_sum_act st a (fun x => P1 x y - P0 x y)]
  simp only [meanFieldMap]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [activateFraction_eq ν M hN st x, cnt_eq ν M π hπ st a ha x]
  unfold configuration
  field_simp
  ring

open MarkovEntanglement in
theorem one_step {N : ℕ} (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (α : ℝ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π) (st : Fin N → S) :
    ∑ s' : Fin N → S, rmabStep P0 P1 π st s' *
        l1Norm (fun x => configuration s' x
          - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)) (configuration st) x)
      ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
  classical
  set M : ℕ := ⌊α * (N : ℝ)⌋₊ with hM
  set φ : S → ℝ := meanFieldMap P0 P1 ν ((M : ℝ) / (N : ℝ)) (configuration st) with hφdef
  have hswap : ∑ s' : Fin N → S, rmabStep P0 P1 π st s' *
        l1Norm (fun x => configuration s' x - φ x)
      = ∑ a : Fin N → Bool, π st a *
          ∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
            (∑ x, |(stateCount s' x : ℝ) / (N : ℝ) - φ x|) := by
    simp only [rmabStep, l1Norm, configuration]
    have h1 : ∀ s' : Fin N → S,
        (∑ a : Fin N → Bool, π st a * ∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
          (∑ x, |(stateCount s' x : ℝ) / (N:ℝ) - φ x|)
        = ∑ a : Fin N → Bool, π st a * ((∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
            (∑ x, |(stateCount s' x : ℝ) / (N:ℝ) - φ x|)) := by
      intro s'
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [Finset.sum_congr rfl (fun s' _ => h1 s'), Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  have hterm : ∀ a : Fin N → Bool, π st a *
      (∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
        (∑ x, |(stateCount s' x : ℝ) / (N : ℝ) - φ x|))
      ≤ π st a * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
    intro a
    by_cases ha : π st a = 0
    · rw [ha]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (hπ.1.1 st a)
      refine cond_bound hN (fun j y => rmabKernel P0 P1 (st j) (a j) y) ?_ ?_ φ ?_
      · intro j y
        unfold rmabKernel
        by_cases h : a j = true <;> simp [h, hP0.1, hP1.1]
      · intro j
        unfold rmabKernel
        by_cases h : a j = true <;> simp [h, hP0.2, hP1.2]
      · intro y
        exact kernel_sum_eq P0 P1 ν M hN π hπ st a ha y
  calc ∑ a : Fin N → Bool, π st a *
        (∑ s' : Fin N → S, (∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) *
          (∑ x, |(stateCount s' x : ℝ) / (N : ℝ) - φ x|))
      ≤ ∑ a : Fin N → Bool, π st a * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
        rw [← Finset.sum_mul, hπ.1.2 st, one_mul]

end ME9

namespace ME10

set_option linter.unusedSectionVars false

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### The sup norm -/

theorem le_supNorm [Nonempty S] (v : S → ℝ) (z : S) : |v z| ≤ supNorm v :=
  le_ciSup (Finite.bddAbove_range (fun x => |v x|)) z

theorem supNorm_le [Nonempty S] {v : S → ℝ} {c : ℝ} (h : ∀ z, |v z| ≤ c) : supNorm v ≤ c :=
  ciSup_le h

theorem supNorm_nonneg [Nonempty S] (v : S → ℝ) : 0 ≤ supNorm v := by
  obtain ⟨z⟩ := ‹Nonempty S›
  exact le_trans (abs_nonneg _) (le_supNorm v z)

theorem exists_ge_of_supNorm_ge [Nonempty S] {v : S → ℝ} {δ : ℝ} (h : δ ≤ supNorm v) :
    ∃ z, δ ≤ |v z| := by
  obtain ⟨z, -, hz⟩ :=
    Finset.exists_max_image (Finset.univ : Finset S) (fun z => |v z|) Finset.univ_nonempty
  exact ⟨z, le_trans h (supNorm_le fun w => hz w (Finset.mem_univ w))⟩

/-! ### A bespoke Hoeffding bound for finite product measures -/

/-- The chord bound for the exponential on `[-1, 1]`. -/
theorem exp_chord {lam y : ℝ} (hy : |y| ≤ 1) :
    Real.exp (lam * y) ≤ Real.cosh lam + y * Real.sinh lam := by
  have h := abs_le.1 hy
  have ha : (0:ℝ) ≤ (1 + y) / 2 := by linarith [h.1]
  have hb : (0:ℝ) ≤ (1 - y) / 2 := by linarith [h.2]
  have hab : (1 + y) / 2 + (1 - y) / 2 = 1 := by ring
  have hcv := convexOn_exp.2 (Set.mem_univ lam) (Set.mem_univ (-lam)) ha hb hab
  simp only [smul_eq_mul] at hcv
  have he : (1 + y) / 2 * lam + (1 - y) / 2 * (-lam) = lam * y := by ring
  rw [he] at hcv
  rw [Real.cosh_eq, Real.sinh_eq]
  linarith

/-- A centred `[-1,1]`-valued observable has sub-Gaussian moment generating function. -/
theorem mgf_bound (lam : ℝ) (κ : S → ℝ) (hnn : ∀ y, 0 ≤ κ y) (hsum : ∑ y, κ y = 1)
    (g : S → ℝ) (hg : ∀ z, |g z| ≤ 1) (hg0 : ∑ z, κ z * g z = 0) :
    ∑ z, κ z * Real.exp (lam * g z) ≤ Real.exp (lam ^ 2 / 2) := by
  calc ∑ z, κ z * Real.exp (lam * g z)
      ≤ ∑ z, κ z * (Real.cosh lam + g z * Real.sinh lam) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (exp_chord (hg z)) (hnn z)
    _ = Real.cosh lam := by
        have hpt : ∀ z : S, κ z * (Real.cosh lam + g z * Real.sinh lam)
            = κ z * Real.cosh lam + (κ z * g z) * Real.sinh lam := fun z => by ring
        rw [Finset.sum_congr rfl (fun z _ => hpt z), Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul, hsum, hg0]
        ring
    _ ≤ Real.exp (lam ^ 2 / 2) := Real.cosh_le_exp_half_sq lam

/-- Chernoff bound for a sum of independent centred `[-1,1]`-valued coordinates. -/
theorem chernoff {N : ℕ} (κ : Fin N → S → ℝ) (hnn : ∀ j y, 0 ≤ κ j y)
    (hsum : ∀ j, ∑ y, κ j y = 1)
    (g : Fin N → S → ℝ) (hg : ∀ j z, |g j z| ≤ 1) (hg0 : ∀ j, ∑ z, κ j z * g j z = 0)
    (lam : ℝ) (hlam : 0 < lam) (c : ℝ) :
    ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => c ≤ ∑ j, g j (s' j)),
        (∏ j, κ j (s' j))
      ≤ Real.exp (-(lam * c)) * Real.exp ((N : ℝ) * lam ^ 2 / 2) := by
  classical
  have hνnn : ∀ s' : Fin N → S, 0 ≤ ∏ j, κ j (s' j) :=
    fun s' => Finset.prod_nonneg fun j _ => hnn j (s' j)
  have hstep1 : ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => c ≤ ∑ j, g j (s' j)),
      (∏ j, κ j (s' j))
      ≤ ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => c ≤ ∑ j, g j (s' j)),
        (∏ j, κ j (s' j)) * Real.exp (lam * ((∑ j, g j (s' j)) - c)) := by
    refine Finset.sum_le_sum fun s' hs' => ?_
    have hc : c ≤ ∑ j, g j (s' j) := (Finset.mem_filter.1 hs').2
    have h1 : (1:ℝ) ≤ Real.exp (lam * ((∑ j, g j (s' j)) - c)) := by
      rw [Real.one_le_exp_iff]
      have : (0:ℝ) ≤ (∑ j, g j (s' j)) - c := by linarith
      positivity
    nlinarith [hνnn s']
  have hstep2 : ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => c ≤ ∑ j, g j (s' j)),
      (∏ j, κ j (s' j)) * Real.exp (lam * ((∑ j, g j (s' j)) - c))
      ≤ ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * Real.exp (lam * ((∑ j, g j (s' j)) - c)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro s' _ _
    exact mul_nonneg (hνnn s') (Real.exp_nonneg _)
  have hstep3 : ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * Real.exp (lam * ((∑ j, g j (s' j)) - c))
      = Real.exp (-(lam * c)) *
        ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * ∏ j, Real.exp (lam * g j (s' j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [← Real.exp_sum]
    have he : lam * ((∑ j, g j (s' j)) - c) = -(lam * c) + ∑ j, lam * g j (s' j) := by
      rw [← Finset.mul_sum]
      ring
    rw [he, Real.exp_add]
    ring
  have hstep4 : ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * ∏ j, Real.exp (lam * g j (s' j))
      = ∏ j, ∑ z, κ j z * Real.exp (lam * g j z) :=
    ME9.prod_expect κ (fun j z => Real.exp (lam * g j z))
  have hstep5 : ∏ j : Fin N, (∑ z, κ j z * Real.exp (lam * g j z))
      ≤ Real.exp ((N : ℝ) * lam ^ 2 / 2) := by
    have h1 : ∏ j : Fin N, (∑ z, κ j z * Real.exp (lam * g j z))
        ≤ ∏ _j : Fin N, Real.exp (lam ^ 2 / 2) := by
      refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => mgf_bound lam (κ j) (hnn j)
        (hsum j) (g j) (hg j) (hg0 j))
      exact Finset.sum_nonneg fun z _ => mul_nonneg (hnn j z) (Real.exp_nonneg _)
    have h2 : ∏ _j : Fin N, Real.exp (lam ^ 2 / 2) = Real.exp ((N : ℝ) * lam ^ 2 / 2) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nsmul]
      congr 1
      push_cast
      ring
    linarith [h1, h2.le, h2.ge]
  calc ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => c ≤ ∑ j, g j (s' j)),
        (∏ j, κ j (s' j))
      ≤ ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * Real.exp (lam * ((∑ j, g j (s' j)) - c)) :=
        le_trans hstep1 hstep2
    _ = Real.exp (-(lam * c)) * ∏ j, ∑ z, κ j z * Real.exp (lam * g j z) := by
        rw [hstep3, hstep4]
    _ ≤ Real.exp (-(lam * c)) * Real.exp ((N : ℝ) * lam ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hstep5 (Real.exp_nonneg _)

/-! ### The one-step deviation is exponentially unlikely -/

theorem tail_one [Nonempty S] {N : ℕ} (hN : 0 < N) (κ : Fin N → S → ℝ)
    (hnn : ∀ j y, 0 ≤ κ j y) (hsum : ∀ j, ∑ y, κ j y = 1)
    (φ : S → ℝ) (hφ : ∀ y, ∑ j, κ j y = (N:ℝ) * φ y) (δ : ℝ) (hδ : 0 < δ)
    (y : S) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
        δ ≤ σ * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)), (∏ j, κ j (s' j))
      ≤ Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by
  classical
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hκle : ∀ j y', κ j y' ≤ 1 := by
    intro j y'
    rw [← hsum j]
    exact Finset.single_le_sum (fun z _ => hnn j z) (Finset.mem_univ y')
  have habs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> simp
  set g : Fin N → S → ℝ := fun j z => σ * ((if z = y then (1:ℝ) else 0) - κ j y) with hgdef
  have hg : ∀ j z, |g j z| ≤ 1 := by
    intro j z
    rw [hgdef]
    simp only [abs_mul, habs, one_mul]
    rw [abs_le]
    by_cases h : z = y
    · simp only [if_pos h]
      constructor <;> linarith [hnn j y, hκle j y]
    · simp only [if_neg h]
      constructor <;> linarith [hnn j y, hκle j y]
  have hg0 : ∀ j, ∑ z, κ j z * g j z = 0 := by
    intro j
    have hpt : ∀ z : S, κ j z * g j z
        = σ * ((if z = y then κ j z else 0) - κ j z * κ j y) := by
      intro z
      rw [hgdef]
      by_cases h : z = y <;> simp [h] <;> ring
    rw [Finset.sum_congr rfl (fun z _ => hpt z), ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ y (fun z => κ j z), ← Finset.sum_mul, hsum j]
    simp
  have hgsum : ∀ s' : Fin N → S,
      ∑ j, g j (s' j) = σ * ((stateCount s' y : ℝ) - (N:ℝ) * φ y) := by
    intro s'
    rw [hgdef]
    simp only []
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← ME9.sum_ind s' y, hφ y]
  have hfil : (Finset.univ.filter (fun s' : Fin N → S =>
        δ ≤ σ * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)))
      = (Finset.univ.filter (fun s' : Fin N → S => (N:ℝ) * δ ≤ ∑ j, g j (s' j))) := by
    ext s'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hgsum s']
    have hre : σ * ((stateCount s' y : ℝ) - (N:ℝ) * φ y)
        = (N:ℝ) * (σ * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)) := by
      field_simp
    rw [hre]
    constructor
    · intro h
      exact mul_le_mul_of_nonneg_left h (le_of_lt hNR)
    · intro h
      exact le_of_mul_le_mul_left h hNR
  rw [hfil]
  refine le_trans (chernoff κ hnn hsum g hg hg0 δ hδ ((N:ℝ) * δ)) ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  ring_nf
  nlinarith [sq_nonneg δ, hNR]

theorem one_step_tail [Nonempty S] {N : ℕ} (hN : 0 < N) (κ : Fin N → S → ℝ)
    (hnn : ∀ j y, 0 ≤ κ j y) (hsum : ∀ j, ∑ y, κ j y = 1)
    (φ : S → ℝ) (hφ : ∀ y, ∑ j, κ j y = (N:ℝ) * φ y) (δ : ℝ) (hδ : 0 < δ) :
    ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
        δ ≤ supNorm (fun y => (stateCount s' y : ℝ) / (N:ℝ) - φ y)), (∏ j, κ j (s' j))
      ≤ 2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by
  classical
  have hνnn : ∀ s' : Fin N → S, 0 ≤ ∏ j, κ j (s' j) :=
    fun s' => Finset.prod_nonneg fun j _ => hnn j (s' j)
  have hind : ∀ s' : Fin N → S,
      δ ≤ supNorm (fun y => (stateCount s' y : ℝ) / (N:ℝ) - φ y) →
      (1:ℝ) ≤ ∑ y : S,
        ((if δ ≤ 1 * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0)
          + (if δ ≤ (-1) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0)) := by
    intro s' hge
    obtain ⟨y, hy⟩ := exists_ge_of_supNorm_ge hge
    have hyterm : (1:ℝ) ≤ (if δ ≤ 1 * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0)
        + (if δ ≤ (-1) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0) := by
      rcases abs_cases ((stateCount s' y : ℝ) / (N:ℝ) - φ y) with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he] at hy
        rw [if_pos (show δ ≤ 1 * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) by linarith)]
        have hz : (0:ℝ) ≤ (if δ ≤ (-1) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)
            then (1:ℝ) else 0) := by positivity
        linarith
      · rw [he] at hy
        rw [if_pos (show δ ≤ (-1) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) by linarith)]
        have hz : (0:ℝ) ≤ (if δ ≤ 1 * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)
            then (1:ℝ) else 0) := by positivity
        linarith
    refine le_trans hyterm (Finset.single_le_sum (f := fun y : S =>
      ((if δ ≤ 1 * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0)
        + (if δ ≤ (-1) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0)))
      (fun z _ => by positivity) (Finset.mem_univ y))
  calc ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
        δ ≤ supNorm (fun y => (stateCount s' y : ℝ) / (N:ℝ) - φ y)), (∏ j, κ j (s' j))
      ≤ ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
          δ ≤ supNorm (fun y => (stateCount s' y : ℝ) / (N:ℝ) - φ y)),
          (∏ j, κ j (s' j)) * ∑ y : S,
            ((if δ ≤ 1 * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0)
              + (if δ ≤ (-1) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0)) := by
        refine Finset.sum_le_sum fun s' hs' => ?_
        have h1 := hind s' (Finset.mem_filter.1 hs').2
        nlinarith [hνnn s']
    _ ≤ ∑ s' : Fin N → S, (∏ j, κ j (s' j)) * ∑ y : S,
          ((if δ ≤ 1 * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0)
            + (if δ ≤ (-1) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y) then (1:ℝ) else 0)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro s' _ _
        refine mul_nonneg (hνnn s') (Finset.sum_nonneg fun y _ => by positivity)
    _ = ∑ y : S, ((∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
            δ ≤ 1 * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)), (∏ j, κ j (s' j)))
          + ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
            δ ≤ (-1) * ((stateCount s' y : ℝ) / (N:ℝ) - φ y)), (∏ j, κ j (s' j))) := by
        simp only [Finset.mul_sum, mul_add]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
        congr 1 <;>
          exact Finset.sum_congr rfl fun s' _ => by split_ifs <;> ring
    _ ≤ ∑ _y : S, (Real.exp (-(N:ℝ) * δ ^ 2 / 2) + Real.exp (-(N:ℝ) * δ ^ 2 / 2)) := by
        refine Finset.sum_le_sum fun y _ => ?_
        exact add_le_add (tail_one hN κ hnn hsum φ hφ δ hδ y 1 (Or.inl rfl))
          (tail_one hN κ hnn hsum φ hφ δ hδ y (-1) (Or.inr rfl))
    _ = 2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-! ### The mean-field map is Lipschitz -/

theorem hpm_lip [Nonempty S] (ν : S → ℝ) (m m' : S → ℝ) (x : S) :
    |higherPriorityMass ν m x - higherPriorityMass ν m' x|
      ≤ (Fintype.card S : ℝ) * supNorm (fun z => m z - m' z) := by
  unfold higherPriorityMass
  rw [← Finset.sum_sub_distrib]
  calc |∑ y ∈ Finset.univ.filter fun y => ν x < ν y, (m y - m' y)|
      ≤ ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, |m y - m' y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, supNorm (fun z => m z - m' z) :=
        Finset.sum_le_sum fun y _ => le_supNorm (fun z => m z - m' z) y
    _ ≤ ∑ _y : S, supNorm (fun z => m z - m' z) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => supNorm_nonneg _)
    _ = (Fintype.card S : ℝ) * supNorm (fun z => m z - m' z) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem af_lip [Nonempty S] (ν : S → ℝ) (β : ℝ) (m m' : S → ℝ) (x : S) :
    |activateFraction ν β m x - activateFraction ν β m' x|
      ≤ (1 + (Fintype.card S : ℝ)) * supNorm (fun z => m z - m' z) := by
  have hs := supNorm_nonneg (fun z => m z - m' z)
  have hcard : (0:ℝ) ≤ (Fintype.card S : ℝ) := by positivity
  have hcs : (0:ℝ) ≤ (Fintype.card S : ℝ) * supNorm (fun z => m z - m' z) :=
    mul_nonneg hcard hs
  unfold activateFraction
  refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le ?_ ?_)
  · have := le_supNorm (fun z => m z - m' z) x
    linarith
  · refine le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le ?_ ?_)
    · simp only [sub_self, abs_zero]
      linarith
    · have he : (β - higherPriorityMass ν m x) - (β - higherPriorityMass ν m' x)
          = -(higherPriorityMass ν m x - higherPriorityMass ν m' x) := by ring
      rw [he, abs_neg]
      linarith [hpm_lip ν m m' x]

theorem mfm_lip [Nonempty S] (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (β : ℝ) (m m' : S → ℝ) :
    supNorm (fun y => meanFieldMap P0 P1 ν β m y - meanFieldMap P0 P1 ν β m' y)
      ≤ ((Fintype.card S : ℝ) * (3 + 2 * (Fintype.card S : ℝ)))
          * supNorm (fun z => m z - m' z) := by
  have hs := supNorm_nonneg (fun z => m z - m' z)
  have hcard : (0:ℝ) ≤ (Fintype.card S : ℝ) := by positivity
  have hP0le : ∀ x y : S, P0 x y ≤ 1 := by
    intro x y
    rw [← hP0.2 x]
    exact Finset.single_le_sum (fun z _ => hP0.1 x z) (Finset.mem_univ y)
  have hP1le : ∀ x y : S, P1 x y ≤ 1 := by
    intro x y
    rw [← hP1.2 x]
    exact Finset.single_le_sum (fun z _ => hP1.1 x z) (Finset.mem_univ y)
  refine supNorm_le fun y => ?_
  have hterm : ∀ x : S, |((m x - activateFraction ν β m x) * P0 x y
        + activateFraction ν β m x * P1 x y)
      - ((m' x - activateFraction ν β m' x) * P0 x y
        + activateFraction ν β m' x * P1 x y)|
      ≤ (3 + 2 * (Fintype.card S : ℝ)) * supNorm (fun z => m z - m' z) := by
    intro x
    have hd : |m x - m' x| ≤ supNorm (fun z => m z - m' z) :=
      le_supNorm (fun z => m z - m' z) x
    have he : |activateFraction ν β m x - activateFraction ν β m' x|
        ≤ (1 + (Fintype.card S : ℝ)) * supNorm (fun z => m z - m' z) := af_lip ν β m m' x
    have hrw : ((m x - activateFraction ν β m x) * P0 x y
          + activateFraction ν β m x * P1 x y)
        - ((m' x - activateFraction ν β m' x) * P0 x y
          + activateFraction ν β m' x * P1 x y)
        = ((m x - m' x) - (activateFraction ν β m x - activateFraction ν β m' x)) * P0 x y
          + (activateFraction ν β m x - activateFraction ν β m' x) * P1 x y := by ring
    rw [hrw]
    have h1 : |((m x - m' x) - (activateFraction ν β m x - activateFraction ν β m' x)) * P0 x y
          + (activateFraction ν β m x - activateFraction ν β m' x) * P1 x y|
        ≤ |(m x - m' x) - (activateFraction ν β m x - activateFraction ν β m' x)| * P0 x y
          + |activateFraction ν β m x - activateFraction ν β m' x| * P1 x y := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hP0.1 x y), abs_of_nonneg (hP1.1 x y)]
    have h2 : |(m x - m' x) - (activateFraction ν β m x - activateFraction ν β m' x)|
        ≤ |m x - m' x| + |activateFraction ν β m x - activateFraction ν β m' x| :=
      abs_sub _ _
    have h3 : |(m x - m' x) - (activateFraction ν β m x - activateFraction ν β m' x)| * P0 x y
        ≤ (|m x - m' x| + |activateFraction ν β m x - activateFraction ν β m' x|) * 1 :=
      mul_le_mul h2 (hP0le x y) (hP0.1 x y) (by positivity)
    have h4 : |activateFraction ν β m x - activateFraction ν β m' x| * P1 x y
        ≤ |activateFraction ν β m x - activateFraction ν β m' x| * 1 :=
      mul_le_mul_of_nonneg_left (hP1le x y) (abs_nonneg _)
    linarith
  simp only [meanFieldMap]
  rw [← Finset.sum_sub_distrib]
  calc |∑ x, (((m x - activateFraction ν β m x) * P0 x y
          + activateFraction ν β m x * P1 x y)
        - ((m' x - activateFraction ν β m' x) * P0 x y
          + activateFraction ν β m' x * P1 x y))|
      ≤ ∑ x, |((m x - activateFraction ν β m x) * P0 x y
          + activateFraction ν β m x * P1 x y)
        - ((m' x - activateFraction ν β m' x) * P0 x y
          + activateFraction ν β m' x * P1 x y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : S, (3 + 2 * (Fintype.card S : ℝ)) * supNorm (fun z => m z - m' z) :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = ((Fintype.card S : ℝ) * (3 + 2 * (Fintype.card S : ℝ)))
          * supNorm (fun z => m z - m' z) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-! ### The `N`-agent chain -/

theorem supNorm_tri [Nonempty S] (a b c : S → ℝ) :
    supNorm (fun x => a x - c x) ≤ supNorm (fun x => a x - b x) + supNorm (fun x => b x - c x) := by
  refine supNorm_le fun z => ?_
  have h1 := le_supNorm (fun x => a x - b x) z
  have h2 := le_supNorm (fun x => b x - c x) z
  have h3 : |a z - c z| ≤ |a z - b z| + |b z - c z| := abs_sub_le _ _ _
  simp only [] at h1 h2
  linarith

theorem rmabStep_nonneg {N : ℕ} (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπnn : ∀ st a, 0 ≤ π st a) (st s' : Fin N → S) : 0 ≤ rmabStep P0 P1 π st s' := by
  unfold rmabStep
  refine Finset.sum_nonneg fun a _ => mul_nonneg (hπnn st a) (Finset.prod_nonneg fun j _ => ?_)
  unfold rmabKernel
  by_cases h : a j = true <;> simp [h, hP0.1, hP1.1]

theorem rmabStep_sum {N : ℕ} (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπsum : ∀ st, ∑ a, π st a = 1) (st : Fin N → S) :
    ∑ s' : Fin N → S, rmabStep P0 P1 π st s' = 1 := by
  unfold rmabStep
  rw [Finset.sum_comm]
  have h1 : ∀ a : Fin N → Bool,
      ∑ s' : Fin N → S, π st a * ∏ j, rmabKernel P0 P1 (st j) (a j) (s' j) = π st a := by
    intro a
    rw [← Finset.mul_sum, ME9.expect_const (fun j y => rmabKernel P0 P1 (st j) (a j) y) ?_, mul_one]
    intro j
    unfold rmabKernel
    by_cases h : a j = true <;> simp [h, hP0.2, hP1.2]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), hπsum st]

theorem rmabLaw_nonneg {N : ℕ} (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπnn : ∀ st a, 0 ≤ π st a) (s0 : Fin N → S) (t : ℕ) (s : Fin N → S) :
    0 ≤ rmabLaw P0 P1 π s0 t s := by
  induction t generalizing s with
  | zero =>
    unfold rmabLaw
    by_cases h : s = s0 <;> simp [h]
  | succ u ih =>
    show 0 ≤ ∑ w, rmabLaw P0 P1 π s0 u w * rmabStep P0 P1 π w s
    exact Finset.sum_nonneg fun w _ => mul_nonneg (ih w) (rmabStep_nonneg P0 P1 hP0 hP1 π hπnn w s)

theorem rmabLaw_sum {N : ℕ} (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπnn : ∀ st a, 0 ≤ π st a) (hπsum : ∀ st, ∑ a, π st a = 1)
    (s0 : Fin N → S) (t : ℕ) : ∑ s : Fin N → S, rmabLaw P0 P1 π s0 t s = 1 := by
  classical
  induction t with
  | zero =>
    show ∑ s : Fin N → S, (if s = s0 then (1:ℝ) else 0) = 1
    rw [Finset.sum_ite_eq' Finset.univ s0 (fun _ => (1:ℝ))]
    simp
  | succ u ih =>
    show ∑ s' : Fin N → S, ∑ w, rmabLaw P0 P1 π s0 u w * rmabStep P0 P1 π w s' = 1
    rw [Finset.sum_comm]
    have h1 : ∀ w : Fin N → S,
        ∑ s' : Fin N → S, rmabLaw P0 P1 π s0 u w * rmabStep P0 P1 π w s'
          = rmabLaw P0 P1 π s0 u w := by
      intro w
      rw [← Finset.mul_sum, rmabStep_sum P0 P1 hP0 hP1 π hπsum w, mul_one]
    rw [Finset.sum_congr rfl (fun w _ => h1 w), ih]

/-- The one-step deviation of the configuration is exponentially unlikely, for any starting
joint state. -/
theorem step_tail [Nonempty S] {N : ℕ} (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (M : ℕ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπ : IsIndexPolicy ν M π)
    (st : Fin N → S) (δ : ℝ) (hδ : 0 < δ) :
    ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => δ ≤ supNorm (fun y =>
        configuration s' y - meanFieldMap P0 P1 ν ((M:ℝ)/(N:ℝ)) (configuration st) y)),
        rmabStep P0 P1 π st s'
      ≤ 2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by
  classical
  have hswap : ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => δ ≤ supNorm (fun y =>
        configuration s' y - meanFieldMap P0 P1 ν ((M:ℝ)/(N:ℝ)) (configuration st) y)),
        rmabStep P0 P1 π st s'
      = ∑ a : Fin N → Bool, π st a *
          ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => δ ≤ supNorm (fun y =>
            configuration s' y
              - meanFieldMap P0 P1 ν ((M:ℝ)/(N:ℝ)) (configuration st) y)),
            (∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)) := by
    unfold rmabStep
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  have hterm : ∀ a : Fin N → Bool, π st a *
      (∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => δ ≤ supNorm (fun y =>
        configuration s' y - meanFieldMap P0 P1 ν ((M:ℝ)/(N:ℝ)) (configuration st) y)),
        (∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)))
      ≤ π st a * (2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2)) := by
    intro a
    by_cases ha : π st a = 0
    · rw [ha]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (hπ.1.1 st a)
      exact one_step_tail hN (fun j y => rmabKernel P0 P1 (st j) (a j) y)
        (fun j y => by unfold rmabKernel; by_cases h : a j = true <;> simp [h, hP0.1, hP1.1])
        (fun j => by unfold rmabKernel; by_cases h : a j = true <;> simp [h, hP0.2, hP1.2])
        (meanFieldMap P0 P1 ν ((M:ℝ)/(N:ℝ)) (configuration st))
        (fun y => ME9.kernel_sum_eq P0 P1 ν M hN π hπ st a ha y) δ hδ
  calc ∑ a : Fin N → Bool, π st a *
        (∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S => δ ≤ supNorm (fun y =>
          configuration s' y - meanFieldMap P0 P1 ν ((M:ℝ)/(N:ℝ)) (configuration st) y)),
          (∏ j, rmabKernel P0 P1 (st j) (a j) (s' j)))
      ≤ ∑ a : Fin N → Bool,
          π st a * (2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2)) :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = 2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by
        rw [← Finset.sum_mul, hπ.1.2 st, one_mul]

/-! ### The multi-step concentration bound -/

theorem multi_step [Nonempty S] (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (M : ℕ) {N : ℕ} (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπ : IsIndexPolicy ν M π)
    (s0 : Fin N → S) (t : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin N → S =>
        (∑ j ∈ Finset.range (t + 1),
          ((Fintype.card S : ℝ) * (3 + 2 * (Fintype.card S : ℝ))) ^ j) * δ ≤
          supNorm (fun x => configuration s x
            - meanFieldIterate (meanFieldMap P0 P1 ν ((M:ℝ)/(N:ℝ))) t (configuration s0) x)),
        rmabLaw P0 P1 π s0 t s
      ≤ 2 * (t : ℝ) * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by
  classical
  set L : ℝ := (Fintype.card S : ℝ) * (3 + 2 * (Fintype.card S : ℝ)) with hLdef
  set φN : (S → ℝ) → S → ℝ := meanFieldMap P0 P1 ν ((M:ℝ)/(N:ℝ)) with hφN
  have hLnn : (0:ℝ) ≤ L := by rw [hLdef]; positivity
  have hE : (0:ℝ) ≤ 2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by positivity
  induction t with
  | zero =>
    have hz : ∀ s ∈ Finset.univ.filter (fun s : Fin N → S =>
        (∑ j ∈ Finset.range (0 + 1), L ^ j) * δ ≤
          supNorm (fun x => configuration s x
            - meanFieldIterate φN 0 (configuration s0) x)),
        rmabLaw P0 P1 π s0 0 s = 0 := by
      intro s hs
      have hcond := (Finset.mem_filter.1 hs).2
      have hne : s ≠ s0 := by
        rintro rfl
        have h0 : supNorm (fun x => configuration s x
            - meanFieldIterate φN 0 (configuration s) x) ≤ 0 :=
          supNorm_le fun z => by simp [meanFieldIterate]
        have hR : (∑ j ∈ Finset.range (0 + 1), L ^ j) = 1 := by simp
        rw [hR, one_mul] at hcond
        linarith
      show (if s = s0 then (1:ℝ) else 0) = 0
      rw [if_neg hne]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    simp
  | succ u ih =>
    have hRnn : (0:ℝ) ≤ ∑ j ∈ Finset.range (u + 1), L ^ j :=
      Finset.sum_nonneg fun j _ => by positivity
    have hRrec : (∑ j ∈ Finset.range (u + 1 + 1), L ^ j)
        = 1 + L * ∑ j ∈ Finset.range (u + 1), L ^ j := by
      rw [Finset.sum_range_succ' (fun j => L ^ j) (u + 1)]
      have hp : ∀ i : ℕ, L ^ (i + 1) = L ^ i * L := fun i => pow_succ L i
      rw [Finset.sum_congr rfl (fun i _ => hp i), ← Finset.sum_mul]
      ring
    have hlaw : ∀ s' : Fin N → S, rmabLaw P0 P1 π s0 (u + 1) s'
        = ∑ w, rmabLaw P0 P1 π s0 u w * rmabStep P0 P1 π w s' := fun s' => rfl
    have hlw := rmabLaw_nonneg P0 P1 hP0 hP1 π hπ.1.1 s0 u
    have hsnn : ∀ w s', 0 ≤ rmabStep P0 P1 π w s' := rmabStep_nonneg P0 P1 hP0 hP1 π hπ.1.1
    have hkey : ∀ w : Fin N → S,
        rmabLaw P0 P1 π s0 u w * (∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
          (∑ j ∈ Finset.range (u + 1 + 1), L ^ j) * δ ≤
            supNorm (fun x => configuration s' x
              - meanFieldIterate φN (u + 1) (configuration s0) x)),
          rmabStep P0 P1 π w s')
        ≤ (if (∑ j ∈ Finset.range (u + 1), L ^ j) * δ ≤
              supNorm (fun x => configuration w x - meanFieldIterate φN u (configuration s0) x)
            then rmabLaw P0 P1 π s0 u w else 0)
          + rmabLaw P0 P1 π s0 u w
            * (2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2)) := by
      intro w
      by_cases hw : (∑ j ∈ Finset.range (u + 1), L ^ j) * δ ≤
          supNorm (fun x => configuration w x - meanFieldIterate φN u (configuration s0) x)
      · rw [if_pos hw]
        have h1 : ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
            (∑ j ∈ Finset.range (u + 1 + 1), L ^ j) * δ ≤
              supNorm (fun x => configuration s' x
                - meanFieldIterate φN (u + 1) (configuration s0) x)),
            rmabStep P0 P1 π w s' ≤ 1 := by
          calc ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
                (∑ j ∈ Finset.range (u + 1 + 1), L ^ j) * δ ≤
                  supNorm (fun x => configuration s' x
                    - meanFieldIterate φN (u + 1) (configuration s0) x)),
                rmabStep P0 P1 π w s'
              ≤ ∑ s' : Fin N → S, rmabStep P0 P1 π w s' :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun s' _ _ => hsnn w s')
            _ = 1 := rmabStep_sum P0 P1 hP0 hP1 π hπ.1.2 w
        nlinarith [hlw w, mul_nonneg (hlw w) hE]
      · rw [if_neg hw]
        push_neg at hw
        have hsub : Finset.univ.filter (fun s' : Fin N → S =>
            (∑ j ∈ Finset.range (u + 1 + 1), L ^ j) * δ ≤
              supNorm (fun x => configuration s' x
                - meanFieldIterate φN (u + 1) (configuration s0) x))
            ⊆ Finset.univ.filter (fun s' : Fin N → S =>
              δ ≤ supNorm (fun y => configuration s' y - φN (configuration w) y)) := by
          intro s' hs'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs' ⊢
          have hiter : meanFieldIterate φN (u + 1) (configuration s0)
              = φN (meanFieldIterate φN u (configuration s0)) := rfl
          rw [hiter] at hs'
          have htri := supNorm_tri (fun x => configuration s' x)
            (fun x => φN (configuration w) x)
            (fun x => φN (meanFieldIterate φN u (configuration s0)) x)
          have hlip : supNorm (fun x => φN (configuration w) x
              - φN (meanFieldIterate φN u (configuration s0)) x)
              ≤ L * supNorm (fun x => configuration w x
                  - meanFieldIterate φN u (configuration s0) x) := by
            rw [hφN, hLdef]
            exact mfm_lip P0 P1 hP0 hP1 ν _ _ _
          have hmul := mul_le_mul_of_nonneg_left hw.le hLnn
          rw [hRrec] at hs'
          linarith [htri, hlip, hmul]
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s' _ _ => hsnn w s')
        have h3 := step_tail P0 P1 hP0 hP1 ν M hN π hπ w δ hδ
        rw [← hφN] at h3
        nlinarith [hlw w, h2, h3]
    calc ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
          (∑ j ∈ Finset.range (u + 1 + 1), L ^ j) * δ ≤
            supNorm (fun x => configuration s' x
              - meanFieldIterate φN (u + 1) (configuration s0) x)),
          rmabLaw P0 P1 π s0 (u + 1) s'
        = ∑ w : Fin N → S, rmabLaw P0 P1 π s0 u w *
            ∑ s' ∈ Finset.univ.filter (fun s' : Fin N → S =>
              (∑ j ∈ Finset.range (u + 1 + 1), L ^ j) * δ ≤
                supNorm (fun x => configuration s' x
                  - meanFieldIterate φN (u + 1) (configuration s0) x)),
              rmabStep P0 P1 π w s' := by
          rw [Finset.sum_congr rfl (fun s' _ => hlaw s'), Finset.sum_comm]
          exact Finset.sum_congr rfl fun w _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ w : Fin N → S,
            ((if (∑ j ∈ Finset.range (u + 1), L ^ j) * δ ≤
                supNorm (fun x => configuration w x
                  - meanFieldIterate φN u (configuration s0) x)
              then rmabLaw P0 P1 π s0 u w else 0)
            + rmabLaw P0 P1 π s0 u w
              * (2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2))) :=
          Finset.sum_le_sum fun w _ => hkey w
      _ = (∑ w ∈ Finset.univ.filter (fun w : Fin N → S =>
              (∑ j ∈ Finset.range (u + 1), L ^ j) * δ ≤
                supNorm (fun x => configuration w x
                  - meanFieldIterate φN u (configuration s0) x)), rmabLaw P0 P1 π s0 u w)
            + 2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_mul,
            rmabLaw_sum P0 P1 hP0 hP1 π hπ.1.1 hπ.1.2 s0 u, one_mul]
      _ ≤ 2 * (u : ℝ) * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2)
            + 2 * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by
          linarith [ih]
      _ = 2 * ((u : ℝ) + 1) * (Fintype.card S : ℝ) * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by ring
      _ = 2 * ((u + 1 : ℕ) : ℝ) * (Fintype.card S : ℝ)
            * Real.exp (-(N:ℝ) * δ ^ 2 / 2) := by push_cast; ring

end ME10

open MarkovEntanglement ME10 in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N : ℕ), 0 < N →
        ∀ (π : (Fin N → S) → (Fin N → Bool) → ℝ),
          IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π →
          ∀ (s0 : Fin N → S) (t : ℕ) (δ : ℝ), 0 < δ →
            ∑ s ∈ Finset.univ.filter (fun s : Fin N → S =>
                (∑ j ∈ Finset.range (t + 1), K ^ j) * δ ≤
                  supNorm (fun x => configuration s x
                    - meanFieldIterate
                        (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)))
                        t (configuration s0) x)),
              rmabLaw P0 P1 π s0 t s
              ≤ 2 * (t : ℝ) * (Fintype.card S : ℝ)
                  * Real.exp (-(N : ℝ) * δ ^ 2 / 2) := by
  classical
  refine ⟨(Fintype.card S : ℝ) * (3 + 2 * (Fintype.card S : ℝ)), by positivity, ?_⟩
  intro N hN π hπ s0 t δ hδ
  by_cases hSne : Nonempty S
  · haveI := hSne
    exact ME10.multi_step P0 P1 hP0 hP1 ν ⌊α * (N : ℝ)⌋₊ hN π hπ s0 t δ hδ
  · rw [not_nonempty_iff] at hSne
    haveI := hSne
    haveI : IsEmpty (Fin N → S) := by
      constructor
      intro f
      exact IsEmpty.false (f ⟨0, hN⟩)
    simp
