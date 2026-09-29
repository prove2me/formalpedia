-- Prove2me | solution 3 for polyDegree_distinguishing_units_bound
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T02:59:59.892311+00:00
-- url     : https://prove2.me/submissions/96435f18-d5ce-4ad1-a8cc-d9ad8bab2f63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polyDegree_distinguishing_units_bound
import Theorems.Thm_minsky_papert_symmetrization
import Theorems.Thm_ns_lemma2_nonneg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

open Finset

namespace PDUBSketch

variable {b : ℕ}

/-- The weight-0 slice is the singleton `{fun _ => false}`. -/
lemma slice_zero :
    ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = 0))
      = {fun _ => false} := by
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_singleton, Finset.card_eq_zero]
  constructor
  · intro h
    funext i
    cases hy : y i
    · rfl
    · exfalso
      have hi : i ∈ (univ : Finset (Fin b)).filter (fun j => y j = true) := by simp [hy]
      rw [h] at hi
      exact Finset.notMem_empty i hi
  · rintro rfl
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    simp

/-- Every `y` in the weight-1 slice equals some `eᵢ`. -/
lemma slice_one_val (g : BoolFunc b)
    (h_units : ∀ i : Fin b, g (Function.update (fun _ => false) i true) = true)
    (y : Fin b → Bool)
    (hy : y ∈ (univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = 1)) :
    g y = true := by
  simp only [mem_filter, mem_univ, true_and] at hy
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hy
  have hyi : y i = true := by
    have : i ∈ univ.filter (fun j => y j = true) := by rw [hi]; exact mem_singleton_self i
    exact (mem_filter.mp this).2
  have hynot : ∀ j, j ≠ i → y j = false := by
    intro j hj
    cases h : y j
    · rfl
    · exfalso
      have : j ∈ univ.filter (fun k => y k = true) := by simp [h]
      rw [hi] at this
      exact hj (mem_singleton.mp this)
  have hy_eq : y = Function.update (fun _ => false) i true := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [hyi]
    · simp only [Function.update, hj, dif_neg hj]
      exact hynot j hj
  rw [hy_eq]
  exact h_units i

/-- `#(slice t) = b.choose t`. -/
lemma card_slice {t : ℕ} (ht : t ≤ b) :
    ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t)).card
    = b.choose t := by
  have hbij : ((univ : Finset (Fin b → Bool)).filter
      (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t)).card
      = ((univ : Finset (Fin b)).powersetCard t).card := by
    refine Finset.card_bij'
      (fun y _ => (univ : Finset (Fin b)).filter (fun i => y i = true))
      (fun T _ => (fun i => decide (i ∈ T)))
      ?_ ?_ ?_ ?_
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.filter_subset _ _, hy⟩
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      simp only [mem_filter, mem_univ, true_and]
      have hTeq : (univ : Finset (Fin b)).filter (fun i => decide (i ∈ T) = true) = T := by
        ext i; simp
      rw [hTeq]; exact hT.2
    · intro y hy
      funext i
      simp only [decide_eq_true_eq, mem_filter, mem_univ, true_and]
      cases h : y i <;> simp [h]
    · intro T hT
      ext i; simp
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end PDUBSketch

open PDUBSketch Classical

theorem solution : polyDegree_distinguishing_units_bound := by
  intro b hb g h_zero h_units
  -- Step 1: extract multilinear rep `p`.
  have hrep : HasPolyRep g (polyDegree g) := by
    unfold polyDegree
    exact Nat.find_spec _
  obtain ⟨p, hp_deg, hp_eval⟩ := hrep
  -- Step 2: Minsky–Papert symmetrization.
  obtain ⟨Q, hQ_deg, hQ_eval⟩ := minsky_papert_symmetrization p
  have hQd : Q.natDegree ≤ polyDegree g := hQ_deg.trans hp_deg
  have hQ_eval' : ∀ t : ℕ, t ≤ b →
      Q.eval (t : ℝ) * ((b.choose t : ℕ) : ℝ) =
        ∑ y ∈ (univ : Finset (Fin b → Bool)).filter
          (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
          (if g y = true then (1 : ℝ) else 0) := by
    intro t ht
    rw [hQ_eval t ht]
    refine Finset.sum_congr rfl ?_
    intro y _
    exact hp_eval y
  -- Step 3a: `Q(0) = 0`.
  have hQ0 : Q.eval 0 = 0 := by
    have h0 := hQ_eval' 0 (Nat.zero_le _)
    rw [slice_zero, Finset.sum_singleton, h_zero, if_neg (by decide), Nat.choose_zero_right,
      Nat.cast_one, mul_one, Nat.cast_zero] at h0
    exact h0
  -- Step 3b: `Q(1) = 1`.
  have hQ1 : Q.eval 1 = 1 := by
    have h1 := hQ_eval' 1 hb
    have hall : ∀ y ∈ (univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = 1),
        (if g y = true then (1 : ℝ) else 0) = 1 := by
      intro y hy
      rw [slice_one_val g h_units y hy]
      simp
    rw [Finset.sum_congr rfl hall, Finset.sum_const, card_slice hb, nsmul_eq_mul, mul_one,
      Nat.choose_one_right, Nat.cast_one] at h1
    have hbne : ((b : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have : Q.eval 1 * (b : ℝ) = (b : ℝ) := h1
    field_simp at this
    tauto
  -- Step 3c: `0 ≤ Q(t) ≤ 1` on the grid.
  have hcbt_pos : ∀ t : ℕ, t ≤ b → (0 : ℝ) < ((b.choose t : ℕ) : ℝ) := by
    intro t ht
    exact_mod_cast Nat.choose_pos ht
  have hQ_lo : ∀ t : ℕ, t ≤ b → 0 ≤ Q.eval (t : ℝ) := by
    intro t ht
    have heq := hQ_eval' t ht
    have hsum_nonneg : (0 : ℝ) ≤ ∑ y ∈ (univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
        (if g y = true then (1 : ℝ) else 0) := by
      refine Finset.sum_nonneg ?_
      intro y _; split_ifs <;> norm_num
    rw [← heq] at hsum_nonneg
    nlinarith [hsum_nonneg, hcbt_pos t ht]
  have hQ_hi : ∀ t : ℕ, t ≤ b → Q.eval (t : ℝ) ≤ 1 := by
    intro t ht
    have heq := hQ_eval' t ht
    have hsum_le : (∑ y ∈ (univ : Finset (Fin b → Bool)).filter
        (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
        (if g y = true then (1 : ℝ) else 0))
        ≤ ((b.choose t : ℕ) : ℝ) := by
      calc (∑ y ∈ (univ : Finset (Fin b → Bool)).filter
          (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
          (if g y = true then (1 : ℝ) else 0))
          ≤ ∑ _y ∈ (univ : Finset (Fin b → Bool)).filter
            (fun y => ((univ : Finset (Fin b)).filter (fun i => y i = true)).card = t),
            (1 : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro y _; split_ifs <;> norm_num
        _ = ((b.choose t : ℕ) : ℝ) := by
            rw [Finset.sum_const, card_slice ht, nsmul_eq_mul, mul_one]
    rw [← heq] at hsum_le
    have hle : Q.eval (t : ℝ) * ((b.choose t : ℕ) : ℝ) ≤ 1 * ((b.choose t : ℕ) : ℝ) := by
      linarith
    exact le_of_mul_le_mul_right hle (hcbt_pos t ht)
  -- Step 4: apply the Nisan–Szegedy Lemma 2 child.
  exact ns_lemma2_nonneg hb Q hQd hQ0 hQ1 hQ_lo hQ_hi
