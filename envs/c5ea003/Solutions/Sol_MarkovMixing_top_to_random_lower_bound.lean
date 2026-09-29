-- Prove2me | solution 1 for MarkovMixing.top_to_random_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T03:16:05.678805+00:00
-- url     : https://prove2.me/submissions/e0ec8a8e-b904-4a02-b4a7-4a6f7f7770e1

import Definitions.Def_mm_lower
import Definitions.Def_mm_stopping
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A lower bound for the top-to-random shuffle (LPW Proposition 7.14)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Paths

variable {W : Type*} [Fintype W] [DecidableEq W]

private lemma snoc_sum {t : ℕ} (f : (Fin (t + 2) → W) → ℝ) :
    ∑ ω : Fin (t + 2) → W, f ω
      = ∑ ω : Fin (t + 1) → W, ∑ y : W, f (Fin.snoc ω y) := by
  let e : ((Fin (t + 1) → W) × W) ≃ (Fin (t + 2) → W) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun ω => (Fin.init ω, ω (Fin.last _))
      left_inv := by intro p; ext <;> simp
      right_inv := by intro ω; simp }
  have := Equiv.sum_comp e f
  rw [← this, Fintype.sum_prod_type]
  rfl

private lemma pathWeight_snoc (Q : Matrix W W ℝ) {t : ℕ}
    (ω : Fin (t + 1) → W) (y : W) :
    pathWeight Q (Fin.snoc ω y : Fin (t + 2) → W)
      = pathWeight Q ω * Q (ω (Fin.last t)) y := by
  simp only [pathWeight]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (i.castSucc : Fin (t + 1)).castSucc = (i.castSucc : Fin (t+1)).castSucc from rfl,
      Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc]
    congr 1
    rw [show (Fin.last t).succ = Fin.last (t + 1) from rfl, Fin.snoc_last]

private lemma group_by_last {t : ℕ} (F : (Fin (t + 1) → W) → ℝ) :
    ∑ ω : Fin (t + 1) → W, F ω
      = ∑ z : W, ∑ ω : Fin (t + 1) → W, (if ω (Fin.last t) = z then F ω else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp

private lemma sum_ite_last (c : ℝ) (f : W → ℝ) (h : W) :
    ∑ y : W, c * f y * (if y = h then (1 : ℝ) else 0) = c * f h := by
  have hcong : ∀ y ∈ (Finset.univ : Finset W), c * f y * (if y = h then (1 : ℝ) else 0)
      = if y = h then c * f h else 0 := by
    intro y _
    by_cases hy : y = h
    · subst hy; simp
    · simp [hy]
  rw [Finset.sum_congr rfl hcong]
  simp

/-- The `t`-step transition probability as a sum over trajectories. -/
private lemma path_pow (Q : Matrix W W ℝ) (t : ℕ) (z p : W) :
    ∑ ω : Fin (t + 1) → W,
        (if ω 0 = z ∧ ω (Fin.last t) = p then pathWeight Q ω else 0)
      = (Q ^ t) z p := by
  induction t generalizing p with
  | zero =>
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) W)
        (fun ω : Fin 1 → W => if ω 0 = z ∧ ω (Fin.last 0) = p then pathWeight Q ω else 0)
        (fun v : W => if v = z then (if p = z then (1 : ℝ) else 0) else 0)]
    · simp only [pow_zero, Matrix.one_apply]
      rw [Finset.sum_ite_eq' Finset.univ z]
      by_cases h : p = z
      · simp [h]
      · simp [h, Ne.symm h]
    · intro ω
      simp only [pathWeight, Finset.univ_eq_empty, Finset.prod_empty,
        Equiv.funUnique_apply]
      show (if ω 0 = z ∧ ω 0 = p then (1 : ℝ) else 0)
          = if ω 0 = z then (if p = z then (1 : ℝ) else 0) else 0
      by_cases h1 : ω 0 = z
      · rw [if_pos h1]
        by_cases h2 : p = z
        · rw [if_pos h2, if_pos ⟨h1, by rw [h1, h2]⟩]
        · rw [if_neg h2, if_neg]
          rintro ⟨-, hcon⟩
          exact h2 (by rw [← hcon, h1])
      · rw [if_neg h1, if_neg]
        rintro ⟨hcon, -⟩
        exact h1 hcon
  | succ t ih =>
    rw [snoc_sum]
    have key : ∀ (ω : Fin (t + 1) → W) (y : W),
        (if (Fin.snoc ω y : Fin (t + 2) → W) 0 = z ∧
              (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = p then
            pathWeight Q (Fin.snoc ω y : Fin (t + 2) → W) else 0)
          = (if ω 0 = z then (1 : ℝ) else 0) * pathWeight Q ω *
              Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0) := by
      intro ω y
      have h0 : (Fin.snoc ω y : Fin (t + 2) → W) 0 = ω 0 := by
        have : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
        rw [this, Fin.snoc_castSucc]
      have hl : (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = y := by simp
      rw [h0, hl, pathWeight_snoc]
      by_cases hx : ω 0 = z <;> by_cases hy : y = p <;> simp [hx, hy] <;> ring
    calc ∑ ω : Fin (t + 1) → W, ∑ y : W, _
        = ∑ ω : Fin (t + 1) → W, ∑ y : W,
            ((if ω 0 = z then (1 : ℝ) else 0) * pathWeight Q ω *
              Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun y _ => key ω y
      _ = ∑ ω : Fin (t + 1) → W,
            ((if ω 0 = z then (1 : ℝ) else 0) * pathWeight Q ω * Q (ω (Fin.last t)) p) :=
          Finset.sum_congr rfl fun ω _ => sum_ite_last _ _ p
      _ = ∑ z' : W, (Q ^ t) z z' * Q z' p := by
          rw [group_by_last (t := t)]
          refine Finset.sum_congr rfl fun z' _ => ?_
          rw [← ih z', Finset.sum_mul]
          refine Finset.sum_congr rfl fun ω _ => ?_
          by_cases hz : ω (Fin.last t) = z'
          · by_cases hx : ω 0 = z <;> simp [hz, hx] <;> ring
          · simp [hz]
      _ = (Q ^ (t + 1)) z p := by rw [pow_succ, Matrix.mul_apply]

/-- The sub-probability of surviving outside `S` up to time `t` and being at `p`. -/
private def surv (Q : Matrix W W ℝ) (z : W) (S : Finset W) (t : ℕ) (p : W) : ℝ :=
  ∑ ω : Fin (t + 1) → W,
    if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) ∧ ω (Fin.last t) = p then
      pathWeight Q ω else 0

private lemma surv_sum (Q : Matrix W W ℝ) (z : W) (S : Finset W) (t : ℕ) :
    ∑ p : W, surv Q z S t p = setAvoidTailProb Q z S t := by
  simp only [surv, setAvoidTailProb]
  rw [group_by_last (t := t)]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hl : ω (Fin.last t) = p
  · rw [if_pos hl]
    by_cases hc : ω 0 = z ∧ ∀ i : Fin (t + 1), ω i ∉ S
    · rw [if_pos ⟨hc.1, hc.2, hl⟩, if_pos hc]
    · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
  · rw [if_neg hl, if_neg (fun h => hl h.2.2)]

private lemma surv_nonneg {Q : Matrix W W ℝ} (hQ : IsStochastic Q) (z : W) (S : Finset W)
    (t : ℕ) (p : W) : 0 ≤ surv Q z S t p := by
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact Finset.prod_nonneg fun i _ => hQ.1 _ _
  · exact le_refl 0

private lemma surv_mem {Q : Matrix W W ℝ} (z : W) (S : Finset W) (t : ℕ) {p : W}
    (hp : p ∈ S) : surv Q z S t p = 0 := by
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [if_neg]
  rintro ⟨-, h2, h3⟩
  exact h2 (Fin.last t) (h3 ▸ hp)

private lemma surv_zero (Q : Matrix W W ℝ) (z : W) (S : Finset W) (p : W) :
    surv Q z S 0 p = if z = p ∧ z ∉ S then (1 : ℝ) else 0 := by
  simp only [surv]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) W)
      (fun ω : Fin 1 → W => if ω 0 = z ∧ (∀ i : Fin 1, ω i ∉ S) ∧ ω (Fin.last 0) = p then
        pathWeight Q ω else 0)
      (fun v : W => if v = z then (if z = p ∧ z ∉ S then (1 : ℝ) else 0) else 0)]
  · rw [Finset.sum_ite_eq' Finset.univ z]
    simp
  · intro ω
    simp only [pathWeight, Finset.univ_eq_empty, Finset.prod_empty, Equiv.funUnique_apply]
    have hl : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [hl]
    show (if ω 0 = z ∧ (∀ i : Fin 1, ω i ∉ S) ∧ ω 0 = p then (1 : ℝ) else 0)
        = if ω 0 = z then (if z = p ∧ z ∉ S then (1 : ℝ) else 0) else 0
    by_cases h1 : ω 0 = z
    · rw [if_pos h1]
      have hall : (∀ i : Fin 1, ω i ∉ S) ↔ z ∉ S := by
        constructor
        · intro h; rw [← h1]; exact h 0
        · intro h i
          have : i = 0 := Subsingleton.elim i 0
          rw [this, h1]; exact h
      by_cases h2 : z = p ∧ z ∉ S
      · rw [if_pos h2, if_pos ⟨h1, hall.mpr h2.2, by rw [h1, h2.1]⟩]
      · rw [if_neg h2, if_neg]
        rintro ⟨-, hS, hp⟩
        exact h2 ⟨by rw [← h1, hp], hall.mp hS⟩
    · rw [if_neg h1, if_neg]
      rintro ⟨hc, -, -⟩
      exact h1 hc

private lemma surv_succ (Q : Matrix W W ℝ) (z : W) (S : Finset W) (t : ℕ) (p : W) :
    surv Q z S (t + 1) p
      = if p ∈ S then 0 else ∑ z' : W, surv Q z S t z' * Q z' p := by
  by_cases hp : p ∈ S
  · rw [if_pos hp, surv_mem z S (t + 1) hp]
  rw [if_neg hp]
  simp only [surv]
  rw [snoc_sum]
  have key : ∀ (ω : Fin (t + 1) → W) (y : W),
      (if (Fin.snoc ω y : Fin (t + 2) → W) 0 = z ∧
            (∀ i : Fin (t + 2), (Fin.snoc ω y : Fin (t + 2) → W) i ∉ S) ∧
            (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = p then
          pathWeight Q (Fin.snoc ω y : Fin (t + 2) → W) else 0)
        = (if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
            pathWeight Q ω * Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0) := by
    intro ω y
    have h0 : (Fin.snoc ω y : Fin (t + 2) → W) 0 = ω 0 := by
      have : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
      rw [this, Fin.snoc_castSucc]
    have hl : (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = y := by simp
    have hall : (∀ i : Fin (t + 2), (Fin.snoc ω y : Fin (t + 2) → W) i ∉ S)
        ↔ ((∀ i : Fin (t + 1), ω i ∉ S) ∧ y ∉ S) := by
      constructor
      · intro h
        refine ⟨fun i => ?_, ?_⟩
        · have := h i.castSucc
          rwa [Fin.snoc_castSucc] at this
        · have := h (Fin.last (t + 1))
          rwa [hl] at this
      · rintro ⟨h1, h2⟩ i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i', hi'⟩ | hi'
        · rw [hi', Fin.snoc_castSucc]; exact h1 i'
        · rw [hi', hl]; exact h2
    rw [h0, hl, pathWeight_snoc]
    simp only [hall]
    have hyS : y = p → y ∉ S := fun h => h ▸ hp
    by_cases hy : y = p
    · by_cases hx : ω 0 = z ∧ ∀ i : Fin (t + 1), ω i ∉ S
      · rw [if_pos ⟨hx.1, ⟨hx.2, hyS hy⟩, hy⟩, if_pos hx, if_pos hy]
        ring
      · rw [if_neg (fun h => hx ⟨h.1, h.2.1.1⟩), if_neg hx]
        ring
    · rw [if_neg (fun h => hy h.2.2), if_neg hy]
      ring
  calc ∑ ω : Fin (t + 1) → W, ∑ y : W, _
      = ∑ ω : Fin (t + 1) → W, ∑ y : W,
          ((if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
            pathWeight Q ω * Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun y _ => key ω y
    _ = ∑ ω : Fin (t + 1) → W,
          ((if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
            pathWeight Q ω * Q (ω (Fin.last t)) p) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        have hc : ∀ y ∈ (Finset.univ : Finset W),
            ((if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
              pathWeight Q ω * Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0))
            = if y = p then ((if ω 0 = z ∧ (∀ i : Fin (t + 1), ω i ∉ S) then (1 : ℝ) else 0) *
                pathWeight Q ω * Q (ω (Fin.last t)) p) else 0 := by
          intro y _
          by_cases hy : y = p
          · subst hy; simp
          · simp [hy]
        rw [Finset.sum_congr rfl hc]
        simp
    _ = ∑ z' : W, surv Q z S t z' * Q z' p := by
        rw [group_by_last (t := t)]
        refine Finset.sum_congr rfl fun z' _ => ?_
        simp only [surv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases hz : ω (Fin.last t) = z'
        · rw [if_pos hz]
          by_cases hx : ω 0 = z ∧ ∀ i : Fin (t + 1), ω i ∉ S
          · rw [if_pos hx, if_pos ⟨hx.1, hx.2, hz⟩, hz]
            ring
          · rw [if_neg hx, if_neg (fun h => hx ⟨h.1, h.2.1⟩)]
            ring
        · rw [if_neg hz, if_neg (fun h => hz h.2.2), zero_mul]


private lemma pow_nonneg_of_stochastic {Q : Matrix W W ℝ} (hQ : IsStochastic Q) (t : ℕ)
    (z p : W) : 0 ≤ (Q ^ t) z p := by
  induction t generalizing p with
  | zero => rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z' _ => mul_nonneg (ih z') (hQ.1 _ _)

end Paths

section TTR

private lemma sum_of_inj {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (φ : α → β) (hφ : Function.Injective φ) (F : β → ℝ)
    (hF : ∀ b : β, (∀ a : α, φ a ≠ b) → F b = 0) :
    ∑ b : β, F b = ∑ a : α, F (φ a) := by
  have h1 : ∑ b ∈ (univ : Finset α).image φ, F b = ∑ a : α, F (φ a) :=
    Finset.sum_image fun a _ a' _ hEq => hφ hEq
  rw [← h1]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro b _ hb
  refine hF b fun a hEq => hb ?_
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hEq⟩


/-! ### The top-to-random shuffle as a right random walk -/

private lemma cyc_inv_zero {n : ℕ} (j : Fin n) :
    (Fin.cycleRange j)⁻¹ (⟨0, j.pos⟩ : Fin n) = j := by
  haveI : NeZero n := NeZero.of_pos j.pos
  have h : Fin.cycleRange j j = (⟨0, j.pos⟩ : Fin n) := Fin.cycleRange_self j
  exact (Equiv.Perm.inv_eq_iff_eq).mpr h.symm

private lemma cyc_inj {n : ℕ} : Function.Injective (Fin.cycleRange : Fin n → Equiv.Perm (Fin n)) := by
  intro j k hjk
  rw [← cyc_inv_zero j, ← cyc_inv_zero k, hjk]

private lemma insert_eq {n : ℕ} (x : Equiv.Perm (Fin n)) (j i : Fin n) :
    topToRandomInsert x j i = (x * Fin.cycleRange j) i := by
  haveI : NeZero n := NeZero.of_pos i.pos
  show _ = x (Fin.cycleRange j i)
  simp only [topToRandomInsert]
  by_cases h1 : i.val < j.val
  · rw [dif_pos h1]
    congr 1
    refine (Fin.ext ?_).symm
    rw [Fin.coe_cycleRange_of_lt (by exact h1)]
  · rw [dif_neg h1]
    by_cases h2 : i = j
    · rw [if_pos h2, h2, Fin.cycleRange_self]
      rfl
    · rw [if_neg h2]
      have : j < i := lt_of_le_of_ne (by omega) (Ne.symm h2)
      rw [Fin.cycleRange_of_gt this]

private lemma ttr_apply {n : ℕ} (x y : Equiv.Perm (Fin n)) :
    topToRandom n x y = if ∃ j : Fin n, y = x * Fin.cycleRange j then (1 : ℝ) / n else 0 := by
  simp only [topToRandom]
  have hfilt : (univ.filter fun j : Fin n => ∀ i : Fin n, y i = topToRandomInsert x j i)
      = univ.filter fun j : Fin n => y = x * Fin.cycleRange j := by
    refine Finset.filter_congr fun j _ => ?_
    constructor
    · intro h; exact Equiv.ext fun i => by rw [h i, insert_eq]
    · intro h i; rw [h, insert_eq]
  rw [hfilt]
  by_cases hex : ∃ j : Fin n, y = x * Fin.cycleRange j
  · obtain ⟨j₀, hj₀⟩ := hex
    have : (univ.filter fun j : Fin n => y = x * Fin.cycleRange j) = {j₀} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp [hj₀], ?_⟩
      intro j hj
      simp only [Finset.mem_filter] at hj
      have : x * Fin.cycleRange j = x * Fin.cycleRange j₀ := by rw [← hj.2, ← hj₀]
      exact cyc_inj (mul_left_cancel this)
    rw [this, if_pos ⟨j₀, hj₀⟩]
    simp
  · rw [if_neg hex]
    have : (univ.filter fun j : Fin n => y = x * Fin.cycleRange j) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun j _ hj => hex ⟨j, hj⟩
    rw [this]
    simp

/-- Forward one-step sum: the walk multiplies on the right by a uniform `cycleRange`. -/
private lemma sum_next {n : ℕ} (z : Equiv.Perm (Fin n)) (g : Equiv.Perm (Fin n) → ℝ) :
    ∑ y : Equiv.Perm (Fin n), topToRandom n z y * g y
      = ∑ j : Fin n, (1 / n : ℝ) * g (z * Fin.cycleRange j) := by
  rw [sum_of_inj (fun j : Fin n => z * Fin.cycleRange j)
      (fun j k hjk => cyc_inj (mul_left_cancel hjk))
      (fun y => topToRandom n z y * g y) ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ttr_apply, if_pos ⟨j, rfl⟩]
  · intro y hy
    show topToRandom n z y * g y = 0
    rw [ttr_apply, if_neg (fun ⟨j, hj⟩ => hy j hj.symm), zero_mul]

/-- Backward one-step sum: reindex the previous state. -/
private lemma sum_prev {n : ℕ} (h : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin n) → ℝ) :
    ∑ z : Equiv.Perm (Fin n), f z * topToRandom n z h
      = ∑ j : Fin n, f (h * (Fin.cycleRange j)⁻¹) * (1 / n : ℝ) := by
  rw [sum_of_inj (fun j : Fin n => h * (Fin.cycleRange j)⁻¹)
      (fun j k hjk => cyc_inj (inv_injective (mul_left_cancel hjk)))
      (fun z => f z * topToRandom n z h) ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ttr_apply, if_pos ⟨j, by group⟩]
  · intro z hz
    show f z * topToRandom n z h = 0
    rw [ttr_apply, if_neg ?_, mul_zero]
    rintro ⟨j, hj⟩
    exact hz j (by rw [hj]; group)

private lemma cyc_inv_mid {n : ℕ} (j i : Fin n) (h1 : 1 ≤ i.val) (h2 : i.val ≤ j.val) :
    (Fin.cycleRange j)⁻¹ i = ⟨i.val - 1, by omega⟩ := by
  refine (Equiv.Perm.inv_eq_iff_eq).mpr (Fin.ext ?_).symm
  rw [Fin.coe_cycleRange_of_lt (show (⟨i.val - 1, by omega⟩ : Fin n) < j from by
    rw [Fin.lt_def]; simp only []; omega)]
  simp only []
  omega

private lemma cyc_inv_hi {n : ℕ} (j i : Fin n) (h1 : j.val < i.val) :
    (Fin.cycleRange j)⁻¹ i = i := by
  refine (Equiv.Perm.inv_eq_iff_eq).mpr ?_
  rw [Fin.cycleRange_of_gt (by rw [Fin.lt_def]; exact h1)]


variable {n : ℕ}

private lemma ttr_stochastic (hn : 0 < n) : IsStochastic (topToRandom n) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine ⟨fun x y => ?_, fun z => ?_⟩
  · rw [ttr_apply]
    split_ifs <;> positivity
  · have h := sum_next z (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- The position of a card after one shuffle: it drops by one when the insertion
goes at or below it, and is unchanged otherwise. -/
private lemma pos_step (z : Equiv.Perm (Fin n)) (c : Fin n) (j : Fin n)
    (hm : 1 ≤ ((z⁻¹ c : Fin n)).val) :
    (((z * Fin.cycleRange j)⁻¹ c : Fin n)).val
      = if (z⁻¹ c).val ≤ j.val then (z⁻¹ c).val - 1 else (z⁻¹ c).val := by
  have hmul : ((z * Fin.cycleRange j)⁻¹ c : Fin n) = (Fin.cycleRange j)⁻¹ (z⁻¹ c) := by
    rw [mul_inv_rev]
    rfl
  rw [hmul]
  by_cases hle : (z⁻¹ c).val ≤ j.val
  · rw [if_pos hle, cyc_inv_mid j (z⁻¹ c) hm hle]
  · rw [if_neg hle, cyc_inv_hi j (z⁻¹ c) (by omega)]

private lemma card_lt (m : ℕ) (hm : m ≤ n) :
    (univ.filter fun j : Fin n => j.val < m).card = m := by
  classical
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if i < m then 1 else 0) n,
    ← Finset.card_filter]
  have h : ((Finset.range n).filter fun i => i < m) = Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h, Finset.card_range]

private lemma card_not_ge (m : ℕ) (hm : m ≤ n) :
    (univ.filter fun j : Fin n => ¬ m ≤ j.val).card = m := by
  classical
  have h : (univ.filter fun j : Fin n => ¬ m ≤ j.val)
      = (univ.filter fun j : Fin n => j.val < m) :=
    Finset.filter_congr fun j _ => by omega
  rw [h, card_lt m hm]

private lemma card_ge (m : ℕ) (hm : m ≤ n) :
    (univ.filter fun j : Fin n => m ≤ j.val).card = n - m := by
  classical
  have h : (univ.filter fun j : Fin n => m ≤ j.val)
      = (univ.filter fun j : Fin n => j.val < m)ᶜ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    omega
  rw [h, Finset.card_compl, card_lt m hm, Fintype.card_fin]

/-- The master one-step identity: any function of the card's position evolves by the
two-point average. -/
private lemma master (hn : 0 < n) (z : Equiv.Perm (Fin n)) (c : Fin n)
    (hm : 1 ≤ ((z⁻¹ c : Fin n)).val) (F : ℕ → ℝ) :
    ∑ y : Equiv.Perm (Fin n), topToRandom n z y * F ((y⁻¹ c).val)
      = ((n - (z⁻¹ c).val : ℕ) : ℝ) / n * F ((z⁻¹ c).val - 1)
        + (((z⁻¹ c).val : ℕ) : ℝ) / n * F ((z⁻¹ c).val) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set m : ℕ := (z⁻¹ c).val with hmdef
  have hmn : m ≤ n := le_of_lt (z⁻¹ c).isLt
  rw [sum_next]
  have hterm : ∀ j : Fin n, (1 / n : ℝ) * F (((z * Fin.cycleRange j)⁻¹ c).val)
      = (1 / n : ℝ) * (if m ≤ j.val then F (m - 1) else F m) := by
    intro j
    rw [pos_step z c j hm]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun j : Fin n => m ≤ j.val)]
  have h1 : ∑ j ∈ univ.filter (fun j : Fin n => m ≤ j.val),
      (1 / n : ℝ) * (if m ≤ j.val then F (m - 1) else F m)
      = ((n - m : ℕ) : ℝ) * ((1 / n : ℝ) * F (m - 1)) := by
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [if_pos (Finset.mem_filter.mp hj).2]), Finset.sum_const, nsmul_eq_mul,
      card_ge m hmn]
  have h2 : ∑ j ∈ univ.filter (fun j : Fin n => ¬ m ≤ j.val),
      (1 / n : ℝ) * (if m ≤ j.val then F (m - 1) else F m)
      = ((m : ℕ) : ℝ) * ((1 / n : ℝ) * F m) := by
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [if_neg (Finset.mem_filter.mp hj).2]), Finset.sum_const, nsmul_eq_mul,
      card_not_ge m hmn]
  rw [h1, h2]
  ring

/-! ### The two Lyapunov functions -/

/-- `g(m) = ∑_{i=1}^m n/(n−i)`, the expected remaining time from position `m`. -/
private def gfun (n : ℕ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, (n : ℝ) / ((n : ℝ) - ((i : ℝ) + 1))

/-- `ψ(m) = ∑_{i=1}^m n i/(n−i)²`, the accumulated conditional variance. -/
private def psifun (n : ℕ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, (n : ℝ) * ((i : ℝ) + 1) / ((n : ℝ) - ((i : ℝ) + 1)) ^ 2

/-- The one-step conditional variance at position `m`. -/
private def vfun (n : ℕ) (m : ℕ) : ℝ := (m : ℝ) / ((n : ℝ) - (m : ℝ))

private lemma gfun_zero (n : ℕ) : gfun n 0 = 0 := by simp [gfun]

private lemma psifun_zero (n : ℕ) : psifun n 0 = 0 := by simp [psifun]

private lemma gfun_succ (n m : ℕ) :
    gfun n (m + 1) = gfun n m + (n : ℝ) / ((n : ℝ) - ((m : ℝ) + 1)) := by
  rw [gfun, gfun, Finset.sum_range_succ]

private lemma psifun_succ (n m : ℕ) :
    psifun n (m + 1)
      = psifun n m + (n : ℝ) * ((m : ℝ) + 1) / ((n : ℝ) - ((m : ℝ) + 1)) ^ 2 := by
  rw [psifun, psifun, Finset.sum_range_succ]

private lemma gfun_nonneg (n m : ℕ) (h : m ≤ n) : 0 ≤ gfun n m := by
  refine Finset.sum_nonneg fun i hi => ?_
  have hi' : i < m := Finset.mem_range.mp hi
  have h1 : ((i : ℝ) + 1) ≤ (n : ℝ) := by
    have : i + 1 ≤ n := by omega
    exact_mod_cast this
  positivity

private lemma psifun_nonneg (n m : ℕ) : 0 ≤ psifun n m := by
  refine Finset.sum_nonneg fun i _ => ?_
  positivity

private lemma vfun_nonneg (n m : ℕ) (h : m ≤ n) : 0 ≤ vfun n m := by
  have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  rw [vfun]
  positivity

/-! ### The one-step identities -/

private lemma master_cast (hn : 0 < n) (z : Equiv.Perm (Fin n)) (c : Fin n) (k : ℕ)
    (hk : ((z⁻¹ c : Fin n)).val = k + 1) (F : ℕ → ℝ) :
    ∑ y : Equiv.Perm (Fin n), topToRandom n z y * F ((y⁻¹ c).val)
      = ((n : ℝ) - ((k : ℝ) + 1)) / n * F k + (((k : ℝ) + 1)) / n * F (k + 1) := by
  have hlt : ((z⁻¹ c : Fin n)).val < n := (z⁻¹ c).isLt
  have hmn : k + 1 ≤ n := by omega
  rw [master hn z c (by omega) F, hk]
  have h1 : ((n - (k + 1) : ℕ) : ℝ) = (n : ℝ) - ((k : ℝ) + 1) := by
    rw [Nat.cast_sub hmn]
    push_cast
    ring
  rw [h1]
  norm_num

private lemma L3 (hn : 0 < n) (z : Equiv.Perm (Fin n)) (c : Fin n) (k : ℕ)
    (hk : ((z⁻¹ c : Fin n)).val = k + 1) (cst : ℝ) :
    ∑ y : Equiv.Perm (Fin n), topToRandom n z y * (gfun n ((y⁻¹ c).val) + cst) ^ 2
      = (gfun n ((z⁻¹ c).val) + cst - 1) ^ 2 + vfun n ((z⁻¹ c).val) := by
  have hlt : ((z⁻¹ c : Fin n)).val < n := (z⁻¹ c).isLt
  have hden : (0 : ℝ) < (n : ℝ) - ((k : ℝ) + 1) := by
    have : (k : ℝ) + 1 < (n : ℝ) := by exact_mod_cast (by omega : k + 1 < n)
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [master_cast hn z c k hk (fun m => (gfun n m + cst) ^ 2), hk, gfun_succ, vfun]
  push_cast
  field_simp
  ring

private lemma L2 (hn : 0 < n) (z : Equiv.Perm (Fin n)) (c : Fin n) (k : ℕ)
    (hk : ((z⁻¹ c : Fin n)).val = k + 1) :
    ∑ y : Equiv.Perm (Fin n), topToRandom n z y * psifun n ((y⁻¹ c).val)
      = psifun n ((z⁻¹ c).val) - vfun n ((z⁻¹ c).val) := by
  have hlt : ((z⁻¹ c : Fin n)).val < n := (z⁻¹ c).isLt
  have hden : (0 : ℝ) < (n : ℝ) - ((k : ℝ) + 1) := by
    have : (k : ℝ) + 1 < (n : ℝ) := by exact_mod_cast (by omega : k + 1 < n)
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [master_cast hn z c k hk (fun m => psifun n m), hk, psifun_succ, vfun]
  push_cast
  field_simp
  ring

/-! ### The Chebyshev bound on the hitting time -/

/-- The absorbing set: the marked card is on top. -/
private def Sset (n : ℕ) (c : Fin n) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun h => (h⁻¹ c).val = 0

private lemma mem_Sset (c : Fin n) (h : Equiv.Perm (Fin n)) :
    h ∈ Sset n c ↔ (h⁻¹ c).val = 0 := by
  simp [Sset]

private def sv (n : ℕ) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ)
    (h : Equiv.Perm (Fin n)) : ℝ :=
  surv (topToRandom n) x₀ (Sset n c) u h

private lemma sv_mem (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ)
    {h : Equiv.Perm (Fin n)} (hh : h ∈ Sset n c) : sv n x₀ c u h = 0 :=
  surv_mem x₀ (Sset n c) u hh

private lemma sv_nonneg (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ)
    (h : Equiv.Perm (Fin n)) : 0 ≤ sv n x₀ c u h :=
  surv_nonneg (ttr_stochastic hn) x₀ (Sset n c) u h

private lemma sv_succ (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ)
    (h : Equiv.Perm (Fin n)) :
    sv n x₀ c (u + 1) h
      = if h ∈ Sset n c then 0 else ∑ z, sv n x₀ c u z * topToRandom n z h :=
  surv_succ (topToRandom n) x₀ (Sset n c) u h

private lemma sv_congr (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ)
    (X Y : Equiv.Perm (Fin n) → ℝ) (h : ∀ z, z ∉ Sset n c → X z = Y z) :
    ∑ z, sv n x₀ c u z * X z = ∑ z, sv n x₀ c u z * Y z := by
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z ∈ Sset n c
  · rw [sv_mem x₀ c u hz]; ring
  · rw [h z hz]

/-- Pushing a weighted sum one step forward. -/
private lemma sum_step (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ)
    (F : Equiv.Perm (Fin n) → ℝ) :
    ∑ h, sv n x₀ c (u + 1) h * F h
      = ∑ z, sv n x₀ c u z * ((∑ h, topToRandom n z h * F h)
          - ∑ h ∈ Sset n c, topToRandom n z h * F h) := by
  classical
  have h1 : ∑ h, sv n x₀ c (u + 1) h * F h
      = ∑ h ∈ (Sset n c)ᶜ, (∑ z, sv n x₀ c u z * topToRandom n z h) * F h := by
    rw [← Finset.sum_add_sum_compl (Sset n c) (fun h => sv n x₀ c (u + 1) h * F h)]
    have hS : ∑ h ∈ Sset n c, sv n x₀ c (u + 1) h * F h = 0 := by
      refine Finset.sum_eq_zero fun h hh => ?_
      rw [sv_mem x₀ c (u + 1) hh, zero_mul]
    rw [hS, zero_add]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [sv_succ, if_neg (Finset.mem_compl.mp hh)]
  rw [h1]
  have h2 : ∀ h : Equiv.Perm (Fin n),
      (∑ z, sv n x₀ c u z * topToRandom n z h) * F h
        = ∑ z, sv n x₀ c u z * (topToRandom n z h * F h) := by
    intro h
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [Finset.sum_congr rfl fun h _ => h2 h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have h3 := Finset.sum_add_sum_compl (Sset n c) (fun h => topToRandom n z h * F h)
  linarith [h3]

private def Rq (n : ℕ) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ) : ℝ :=
  ∑ h, sv n x₀ c u h

private def Bq (n : ℕ) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ) : ℝ :=
  ∑ h, sv n x₀ c u h * psifun n ((h⁻¹ c).val)

private def Vterm (n : ℕ) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ) : ℝ :=
  ∑ z, sv n x₀ c u z * vfun n ((z⁻¹ c).val)

private def Aq (n : ℕ) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (K : ℝ) (u : ℕ) : ℝ :=
  ∑ h, sv n x₀ c u h * (gfun n ((h⁻¹ c).val) + (u : ℝ) - K) ^ 2

private def Dq (n : ℕ) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (K : ℝ) (u : ℕ) : ℝ :=
  ∑ s ∈ Finset.range u, (Rq n x₀ c s - Rq n x₀ c (s + 1)) * (((s : ℝ) + 1) - K) ^ 2

private lemma absorb_eq (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ) :
    Rq n x₀ c u - Rq n x₀ c (u + 1)
      = ∑ z, sv n x₀ c u z * ∑ h ∈ Sset n c, topToRandom n z h := by
  have h := sum_step x₀ c u (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [Rq, Rq, h]
  have h2 : ∀ z : Equiv.Perm (Fin n),
      sv n x₀ c u z * ((∑ h, topToRandom n z h) - ∑ h ∈ Sset n c, topToRandom n z h)
        = sv n x₀ c u z - sv n x₀ c u z * ∑ h ∈ Sset n c, topToRandom n z h := by
    intro z
    rw [(ttr_stochastic hn).2 z]
    ring
  rw [Finset.sum_congr rfl fun z _ => h2 z, Finset.sum_sub_distrib]
  ring

private lemma Bq_step (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ) :
    Bq n x₀ c (u + 1) = Bq n x₀ c u - Vterm n x₀ c u := by
  have h := sum_step x₀ c u (fun h => psifun n ((h⁻¹ c).val))
  rw [Bq, h]
  have hS : ∀ z : Equiv.Perm (Fin n),
      ∑ h ∈ Sset n c, topToRandom n z h * psifun n ((h⁻¹ c).val) = 0 := by
    intro z
    refine Finset.sum_eq_zero fun h hh => ?_
    rw [(mem_Sset c h).mp hh, psifun_zero, mul_zero]
  have hmain : ∀ z, z ∉ Sset n c →
      ((∑ h, topToRandom n z h * psifun n ((h⁻¹ c).val))
        - ∑ h ∈ Sset n c, topToRandom n z h * psifun n ((h⁻¹ c).val))
      = psifun n ((z⁻¹ c).val) - vfun n ((z⁻¹ c).val) := by
    intro z hz
    rw [hS z, sub_zero]
    have hpos : (z⁻¹ c).val ≠ 0 := fun hc => hz ((mem_Sset c z).mpr hc)
    obtain ⟨k, hk⟩ : ∃ k, (z⁻¹ c).val = k + 1 := ⟨(z⁻¹ c).val - 1, by omega⟩
    exact L2 hn z c k hk
  rw [sv_congr x₀ c u _ _ hmain]
  have hsplit : ∀ z : Equiv.Perm (Fin n),
      sv n x₀ c u z * (psifun n ((z⁻¹ c).val) - vfun n ((z⁻¹ c).val))
        = sv n x₀ c u z * psifun n ((z⁻¹ c).val)
          - sv n x₀ c u z * vfun n ((z⁻¹ c).val) := fun z => by ring
  rw [Finset.sum_congr rfl fun z _ => hsplit z, Finset.sum_sub_distrib, Bq, Vterm]

private lemma Aq_step (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (K : ℝ) (u : ℕ) :
    Aq n x₀ c K (u + 1)
      = Aq n x₀ c K u + Vterm n x₀ c u
        - (((u : ℝ) + 1) - K) ^ 2 * (Rq n x₀ c u - Rq n x₀ c (u + 1)) := by
  have h := sum_step x₀ c u (fun h => (gfun n ((h⁻¹ c).val) + ((u : ℝ) + 1) - K) ^ 2)
  have hAq : Aq n x₀ c K (u + 1)
      = ∑ h, sv n x₀ c (u + 1) h * (gfun n ((h⁻¹ c).val) + ((u : ℝ) + 1) - K) ^ 2 := by
    rw [Aq]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hc : ((u + 1 : ℕ) : ℝ) = (u : ℝ) + 1 := by push_cast; ring
    rw [hc]
  rw [hAq, h]
  have hS : ∀ z : Equiv.Perm (Fin n),
      ∑ h ∈ Sset n c, topToRandom n z h * (gfun n ((h⁻¹ c).val) + ((u : ℝ) + 1) - K) ^ 2
        = (((u : ℝ) + 1) - K) ^ 2 * ∑ h ∈ Sset n c, topToRandom n z h := by
    intro z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [(mem_Sset c h).mp hh, gfun_zero]
    ring
  have hmain : ∀ z, z ∉ Sset n c →
      ((∑ h, topToRandom n z h * (gfun n ((h⁻¹ c).val) + ((u : ℝ) + 1) - K) ^ 2)
        - ∑ h ∈ Sset n c, topToRandom n z h * (gfun n ((h⁻¹ c).val) + ((u : ℝ) + 1) - K) ^ 2)
      = ((gfun n ((z⁻¹ c).val) + (u : ℝ) - K) ^ 2 + vfun n ((z⁻¹ c).val))
        - (((u : ℝ) + 1) - K) ^ 2 * ∑ h ∈ Sset n c, topToRandom n z h := by
    intro z hz
    rw [hS z]
    congr 1
    have hpos : (z⁻¹ c).val ≠ 0 := fun hc => hz ((mem_Sset c z).mpr hc)
    obtain ⟨k, hk⟩ : ∃ k, (z⁻¹ c).val = k + 1 := ⟨(z⁻¹ c).val - 1, by omega⟩
    have hL := L3 hn z c k hk (((u : ℝ) + 1) - K)
    have he : ∀ y : Equiv.Perm (Fin n),
        gfun n ((y⁻¹ c).val) + (((u : ℝ) + 1) - K)
          = gfun n ((y⁻¹ c).val) + ((u : ℝ) + 1) - K := fun y => by ring
    simp only [he] at hL
    rw [hL]
    congr 2
    ring
  rw [sv_congr x₀ c u _ _ hmain]
  have hsplit : ∀ z : Equiv.Perm (Fin n),
      sv n x₀ c u z * (((gfun n ((z⁻¹ c).val) + (u : ℝ) - K) ^ 2 + vfun n ((z⁻¹ c).val))
        - (((u : ℝ) + 1) - K) ^ 2 * ∑ h ∈ Sset n c, topToRandom n z h)
      = sv n x₀ c u z * (gfun n ((z⁻¹ c).val) + (u : ℝ) - K) ^ 2
        + sv n x₀ c u z * vfun n ((z⁻¹ c).val)
        - (((u : ℝ) + 1) - K) ^ 2
            * (sv n x₀ c u z * ∑ h ∈ Sset n c, topToRandom n z h) := fun z => by ring
  rw [Finset.sum_congr rfl fun z _ => hsplit z, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← absorb_eq hn]
  rw [Aq, Vterm]

private lemma Rq_zero (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (hx : x₀ ∉ Sset n c) :
    Rq n x₀ c 0 = 1 := by
  have key : ∀ y : Equiv.Perm (Fin n), sv n x₀ c 0 y = if x₀ = y then (1 : ℝ) else 0 := by
    intro y
    rw [sv, surv_zero]
    by_cases hh : x₀ = y
    · rw [if_pos ⟨hh, hx⟩, if_pos hh]
    · rw [if_neg (fun hc => hh hc.1), if_neg hh]
  rw [Rq, Finset.sum_congr rfl fun y _ => key y,
    Finset.sum_ite_eq Finset.univ x₀ (fun _ => (1 : ℝ))]
  simp

private lemma Bq_zero (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (hx : x₀ ∉ Sset n c) :
    Bq n x₀ c 0 = psifun n ((x₀⁻¹ c).val) := by
  have key : ∀ y : Equiv.Perm (Fin n),
      sv n x₀ c 0 y * psifun n ((y⁻¹ c).val)
        = if x₀ = y then psifun n ((x₀⁻¹ c).val) else 0 := by
    intro y
    rw [sv, surv_zero]
    by_cases hh : x₀ = y
    · rw [if_pos ⟨hh, hx⟩, if_pos hh, one_mul, hh]
    · rw [if_neg (fun hc => hh hc.1), if_neg hh, zero_mul]
  rw [Bq, Finset.sum_congr rfl fun y _ => key y,
    Finset.sum_ite_eq Finset.univ x₀ (fun _ => psifun n ((x₀⁻¹ c).val))]
  simp

private lemma Aq_zero (x₀ : Equiv.Perm (Fin n)) (c : Fin n) :
    Aq n x₀ c (gfun n ((x₀⁻¹ c).val)) 0 = 0 := by
  rw [Aq]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hh : x₀ = y
  · rw [← hh]
    have hz : gfun n ((x₀⁻¹ c).val) + ((0 : ℕ) : ℝ) - gfun n ((x₀⁻¹ c).val) = 0 := by
      push_cast; ring
    rw [hz]
    ring
  · rw [sv, surv_zero, if_neg (fun hc => hh hc.1), zero_mul]

private lemma Aq_nonneg (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (K : ℝ) (u : ℕ) :
    0 ≤ Aq n x₀ c K u :=
  Finset.sum_nonneg fun h _ => mul_nonneg (sv_nonneg hn x₀ c u h) (sq_nonneg _)

private lemma Bq_nonneg (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ) :
    0 ≤ Bq n x₀ c u :=
  Finset.sum_nonneg fun h _ => mul_nonneg (sv_nonneg hn x₀ c u h) (psifun_nonneg n _)

private lemma Rq_antitone (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (u : ℕ) :
    Rq n x₀ c (u + 1) ≤ Rq n x₀ c u := by
  have h := absorb_eq hn x₀ c u
  have hnn : 0 ≤ ∑ z, sv n x₀ c u z * ∑ h ∈ Sset n c, topToRandom n z h :=
    Finset.sum_nonneg fun z _ => mul_nonneg (sv_nonneg hn x₀ c u z)
      (Finset.sum_nonneg fun h _ => (ttr_stochastic hn).1 z h)
  linarith

private lemma Vsum_eq (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (t : ℕ) :
    ∑ s ∈ Finset.range t, Vterm n x₀ c s = Bq n x₀ c 0 - Bq n x₀ c t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, Bq_step hn]
    ring

private lemma ADq_eq (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (K : ℝ) (t : ℕ) :
    Aq n x₀ c K t + Dq n x₀ c K t
      = Aq n x₀ c K 0 + ∑ s ∈ Finset.range t, Vterm n x₀ c s := by
  induction t with
  | zero => simp [Dq]
  | succ t ih =>
    rw [Aq_step hn, Dq, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Dq] at ih
    linarith [ih]

private lemma Rq_tel (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (t : ℕ) :
    Rq n x₀ c 0 - Rq n x₀ c t
      = ∑ s ∈ Finset.range t, (Rq n x₀ c s - Rq n x₀ c (s + 1)) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_range_succ, ← ih]; ring

private lemma Dq_ge (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n) (K : ℝ) (t : ℕ)
    (hKt : (t : ℝ) < K) :
    (Rq n x₀ c 0 - Rq n x₀ c t) * (K - (t : ℝ)) ^ 2 ≤ Dq n x₀ c K t := by
  rw [Rq_tel x₀ c t, Finset.sum_mul, Dq]
  refine Finset.sum_le_sum fun s hs => ?_
  have hst : s < t := Finset.mem_range.mp hs
  have hnn : 0 ≤ Rq n x₀ c s - Rq n x₀ c (s + 1) := by
    have := Rq_antitone hn x₀ c s
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hnn
  have h1 : ((s : ℝ) + 1) ≤ (t : ℝ) := by
    have : (s : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hst
    linarith
  have h2 : 0 < K - (t : ℝ) := by linarith
  nlinarith [h1, h2]

/-- The Chebyshev bound: the marked card is unlikely to have reached the top. -/
private lemma cheb (hn : 0 < n) (x₀ : Equiv.Perm (Fin n)) (c : Fin n)
    (hx : x₀ ∉ Sset n c) (t : ℕ) (hKt : (t : ℝ) < gfun n ((x₀⁻¹ c).val)) :
    1 - setAvoidTailProb (topToRandom n) x₀ (Sset n c) t
      ≤ psifun n ((x₀⁻¹ c).val) / (gfun n ((x₀⁻¹ c).val) - (t : ℝ)) ^ 2 := by
  set K : ℝ := gfun n ((x₀⁻¹ c).val) with hK
  have hRq : Rq n x₀ c t = setAvoidTailProb (topToRandom n) x₀ (Sset n c) t := by
    rw [Rq]
    exact surv_sum (topToRandom n) x₀ (Sset n c) t
  have h1 := Dq_ge hn x₀ c K t hKt
  have h2 := ADq_eq hn x₀ c K t
  have h3 := Vsum_eq hn x₀ c t
  have h4 := Aq_nonneg hn x₀ c K t
  have h5 := Bq_nonneg hn x₀ c t
  have h6 : Aq n x₀ c K 0 = 0 := Aq_zero x₀ c
  have h7 : Bq n x₀ c 0 = psifun n ((x₀⁻¹ c).val) := Bq_zero x₀ c hx
  have h8 : Rq n x₀ c 0 = 1 := Rq_zero x₀ c hx
  have hpos : (0 : ℝ) < (K - (t : ℝ)) ^ 2 := by
    have : 0 < K - (t : ℝ) := by linarith
    positivity
  rw [← hRq, le_div_iff₀ hpos]
  rw [h8] at h1
  linarith [h1, h2, h3, h4, h5, h6, h7]

/-! ### The order of the bottom block is preserved -/

private lemma cyc_inv_mono (jj : Fin n) {a b : Fin n} (ha : 1 ≤ a.val) (hab : a.val < b.val) :
    (((Fin.cycleRange jj)⁻¹ a).val) < (((Fin.cycleRange jj)⁻¹ b).val) := by
  by_cases hb : b.val ≤ jj.val
  · have ha' : a.val ≤ jj.val := by omega
    rw [cyc_inv_mid jj a ha ha', cyc_inv_mid jj b (by omega) hb]
    simp only []
    omega
  · rw [cyc_inv_hi jj b (by omega)]
    by_cases ha2 : a.val ≤ jj.val
    · rw [cyc_inv_mid jj a ha ha2]
      simp only []
      omega
    · rw [cyc_inv_hi jj a (by omega)]
      exact hab

/-- The `j` cards originally at the bottom. -/
private def card (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n)) (i : Fin j) : Fin n :=
  x₀ ⟨n - j + i.val, by have := i.isLt; omega⟩

private lemma card_inj (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n)) :
    Function.Injective (card n j hj x₀) := by
  intro a b hab
  simp only [card] at hab
  have := x₀.injective hab
  have h2 : n - j + a.val = n - j + b.val := congrArg Fin.val this
  exact Fin.ext (by omega)

/-- The set of decks in which the marked cards appear in their original order. -/
private def Aset (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun h => ∀ a b : Fin j, a.val < b.val →
    ((h⁻¹ (card n j hj x₀ a)).val) < ((h⁻¹ (card n j hj x₀ b)).val)

private lemma mem_Aset (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n))
    (h : Equiv.Perm (Fin n)) :
    h ∈ Aset n j hj x₀ ↔ ∀ a b : Fin j, a.val < b.val →
      ((h⁻¹ (card n j hj x₀ a)).val) < ((h⁻¹ (card n j hj x₀ b)).val) := by
  simp [Aset]

private lemma start_mem (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n)) :
    x₀ ∈ Aset n j hj x₀ := by
  rw [mem_Aset]
  intro a b hab
  have key : ∀ i : Fin j, ((x₀⁻¹ (card n j hj x₀ i)).val) = n - j + i.val := by
    intro i
    simp [card]
  rw [key, key]
  omega

/-- One step of the shuffle preserves the order of a block of cards that are all
strictly below the top. -/
private lemma step_preserves (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n))
    (hjpos : 0 < j) (z : Equiv.Perm (Fin n)) (jj : Fin n)
    (hz : z ∈ Aset n j hj x₀)
    (htop : 1 ≤ ((z⁻¹ (card n j hj x₀ ⟨0, hjpos⟩)).val)) :
    z * Fin.cycleRange jj ∈ Aset n j hj x₀ := by
  rw [mem_Aset]
  intro a b hab
  have hmul : ∀ i : Fin j, (((z * Fin.cycleRange jj)⁻¹ (card n j hj x₀ i)) : Fin n)
      = (Fin.cycleRange jj)⁻¹ (z⁻¹ (card n j hj x₀ i)) := by
    intro i
    rw [mul_inv_rev]
    rfl
  rw [hmul, hmul]
  have hordz := (mem_Aset n j hj x₀ z).mp hz
  have ha1 : 1 ≤ ((z⁻¹ (card n j hj x₀ a)).val) := by
    rcases Nat.eq_zero_or_pos a.val with h0 | h0
    · have : a = ⟨0, hjpos⟩ := Fin.ext h0
      rw [this]
      exact htop
    · have := hordz ⟨0, hjpos⟩ a (by simpa using h0)
      omega
  exact cyc_inv_mono jj ha1 (hordz a b hab)

private lemma path_invariant (n j : ℕ) (hj : j ≤ n) (hjpos : 0 < j)
    (x₀ : Equiv.Perm (Fin n)) {t : ℕ} (ω : Fin (t + 1) → Equiv.Perm (Fin n))
    (h0 : ω 0 = x₀)
    (havoid : ∀ i : Fin (t + 1), ω i ∉ Sset n (card n j hj x₀ ⟨0, hjpos⟩))
    (hw : pathWeight (topToRandom n) ω ≠ 0) :
    ∀ (m : ℕ) (hm : m < t + 1), ω ⟨m, hm⟩ ∈ Aset n j hj x₀ := by
  intro m
  induction m with
  | zero =>
    intro hm
    rw [show (⟨0, hm⟩ : Fin (t + 1)) = 0 from rfl, h0]
    exact start_mem n j hj x₀
  | succ m ih =>
    intro hm
    have hm' : m < t + 1 := by omega
    have hlt : m < t := by omega
    have hprev := ih hm'
    have hfac : topToRandom n (ω ⟨m, hm'⟩) (ω ⟨m + 1, hm⟩) ≠ 0 := by
      intro hc
      refine hw ?_
      rw [pathWeight]
      refine Finset.prod_eq_zero (Finset.mem_univ (⟨m, hlt⟩ : Fin t)) ?_
      exact hc
    obtain ⟨jj, hjj⟩ : ∃ jj : Fin n, ω ⟨m + 1, hm⟩ = ω ⟨m, hm'⟩ * Fin.cycleRange jj := by
      by_contra hcon
      push_neg at hcon
      rw [ttr_apply, if_neg (fun hex => by obtain ⟨jj, hjjj⟩ := hex; exact hcon jj hjjj)] at hfac
      exact hfac rfl
    rw [hjj]
    refine step_preserves n j hj x₀ hjpos _ jj hprev ?_
    have hav := havoid ⟨m, hm'⟩
    rw [mem_Sset] at hav
    omega

private lemma tail_le_A (n j : ℕ) (hj : j ≤ n) (hjpos : 0 < j)
    (x₀ : Equiv.Perm (Fin n)) (hn : 0 < n) (t : ℕ) :
    setAvoidTailProb (topToRandom n) x₀ (Sset n (card n j hj x₀ ⟨0, hjpos⟩)) t
      ≤ ∑ h ∈ Aset n j hj x₀, ((topToRandom n) ^ t) x₀ h := by
  classical
  have hpw : ∀ ω : Fin (t + 1) → Equiv.Perm (Fin n), 0 ≤ pathWeight (topToRandom n) ω :=
    fun ω => Finset.prod_nonneg fun i _ => (ttr_stochastic hn).1 _ _
  have hrhs : ∑ h ∈ Aset n j hj x₀, ((topToRandom n) ^ t) x₀ h
      = ∑ ω : Fin (t + 1) → Equiv.Perm (Fin n),
          (if ω 0 = x₀ ∧ ω (Fin.last t) ∈ Aset n j hj x₀ then
            pathWeight (topToRandom n) ω else 0) := by
    rw [Finset.sum_congr rfl fun h _ => (path_pow (topToRandom n) t x₀ h).symm,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hc : ω 0 = x₀ ∧ ω (Fin.last t) ∈ Aset n j hj x₀
    · rw [if_pos hc]
      have key : ∀ h ∈ Aset n j hj x₀,
          (if ω 0 = x₀ ∧ ω (Fin.last t) = h then pathWeight (topToRandom n) ω else 0)
            = (if h = ω (Fin.last t) then pathWeight (topToRandom n) ω else 0) := by
        intro h _
        by_cases hh : ω (Fin.last t) = h
        · rw [if_pos ⟨hc.1, hh⟩, if_pos hh.symm]
        · rw [if_neg (fun hcc => hh hcc.2),
            if_neg (fun hcc : h = ω (Fin.last t) => hh hcc.symm)]
      rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (Aset n j hj x₀) (ω (Fin.last t))
        (fun _ => pathWeight (topToRandom n) ω), if_pos hc.2]
    · rw [if_neg hc]
      refine Finset.sum_eq_zero fun h hh => ?_
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact hc ⟨e1, by rw [e2]; exact hh⟩
  rw [hrhs, setAvoidTailProb]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hs : ω 0 = x₀ ∧ ∀ i : Fin (t + 1), ω i ∉ Sset n (card n j hj x₀ ⟨0, hjpos⟩)
  · rw [if_pos hs]
    by_cases hzero : pathWeight (topToRandom n) ω = 0
    · rw [hzero]
      split_ifs
      · exact le_refl 0
      · exact le_refl 0
    · have hA := path_invariant n j hj hjpos x₀ ω hs.1 hs.2 hzero t (by omega)
      have hlast : (⟨t, by omega⟩ : Fin (t + 1)) = Fin.last t := rfl
      rw [hlast] at hA
      rw [if_pos ⟨hs.1, hA⟩]
  · rw [if_neg hs]
    split_ifs
    · exact hpw ω
    · exact le_refl 0

/-! ### Counting: the marked cards are in their original order with probability `1/j!` -/

private lemma strictMono_perm_eq_one {j : ℕ} (w : Equiv.Perm (Fin j))
    (hw : ∀ a b : Fin j, a.val < b.val → (w a).val < (w b).val) : ∀ i : Fin j, w i = i := by
  have hle : ∀ m : ℕ, ∀ hm : m < j, m ≤ (w ⟨m, hm⟩).val := by
    intro m
    induction m with
    | zero => intro _; omega
    | succ m ih =>
      intro hm
      have hm' : m < j := by omega
      have h1 := ih hm'
      have h2 := hw ⟨m, hm'⟩ ⟨m + 1, hm⟩ (by simp)
      omega
  have hsum : ∑ i : Fin j, (w i).val = ∑ i : Fin j, i.val :=
    Equiv.sum_comp w (fun i : Fin j => i.val)
  have hpt : ∀ i ∈ (univ : Finset (Fin j)), i.val ≤ (w i).val := by
    intro i _
    have := hle i.val i.isLt
    simpa using this
  have heq := (Finset.sum_eq_sum_iff_of_le hpt).mp hsum.symm
  intro i
  exact Fin.ext (heq i (Finset.mem_univ i)).symm

private def cardEquiv (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n)) :
    Fin j ≃ {x : Fin n // x ∈ Finset.image (card n j hj x₀) univ} := by
  refine Equiv.ofBijective (fun i => ⟨card n j hj x₀ i, Finset.mem_image_of_mem _
    (Finset.mem_univ i)⟩) ⟨?_, ?_⟩
  · intro a b hab
    exact card_inj n j hj x₀ (congrArg Subtype.val hab)
  · rintro ⟨x, hx⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
    exact ⟨i, Subtype.ext hi⟩

private def Tperm (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin j)) : Equiv.Perm (Fin n) :=
  σ.extendDomain (cardEquiv n j hj x₀)

private lemma Tperm_card (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin j)) (i : Fin j) :
    Tperm n j hj x₀ σ (card n j hj x₀ i) = card n j hj x₀ (σ i) := by
  show σ.extendDomain (cardEquiv n j hj x₀) (card n j hj x₀ i) = card n j hj x₀ (σ i)
  exact Equiv.Perm.extendDomain_apply_image σ (cardEquiv n j hj x₀) i

private lemma Tperm_inv_card (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin j)) (i : Fin j) :
    (Tperm n j hj x₀ σ)⁻¹ (card n j hj x₀ i) = card n j hj x₀ (σ⁻¹ i) := by
  refine (Equiv.Perm.inv_eq_iff_eq).mpr ?_
  rw [Tperm_card]
  simp

private lemma Aset_card (n j : ℕ) (hj : j ≤ n) (x₀ : Equiv.Perm (Fin n)) :
    (Aset n j hj x₀).card * Nat.factorial j ≤ Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hcard : (Aset n j hj x₀ ×ˢ (univ : Finset (Equiv.Perm (Fin j)))).card
      = (Aset n j hj x₀).card * Nat.factorial j := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← hcard, ← Finset.card_univ (α := Equiv.Perm (Fin n))]
  refine Finset.card_le_card_of_injOn
    (fun p => Tperm n j hj x₀ p.2 * p.1) (fun p _ => Finset.mem_univ _) ?_
  rintro ⟨h, σ⟩ hp ⟨h', σ'⟩ hp' heq
  simp only [Finset.mem_coe, Finset.mem_product] at hp hp'
  have hA := (mem_Aset n j hj x₀ h).mp hp.1
  have hA' := (mem_Aset n j hj x₀ h').mp hp'.1
  have hpos : ∀ (g : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin j)) (i : Fin j),
      ((Tperm n j hj x₀ τ * g)⁻¹ (card n j hj x₀ i))
        = g⁻¹ (card n j hj x₀ (τ⁻¹ i)) := by
    intro g τ i
    rw [mul_inv_rev]
    show (g⁻¹ ((Tperm n j hj x₀ τ)⁻¹ (card n j hj x₀ i))) = _
    rw [Tperm_inv_card]
  have hkey : ∀ i : Fin j,
      (h⁻¹ (card n j hj x₀ (σ⁻¹ i))) = (h'⁻¹ (card n j hj x₀ (σ'⁻¹ i))) := by
    intro i
    have := congrArg (fun g : Equiv.Perm (Fin n) => g⁻¹ (card n j hj x₀ i)) heq
    simp only [] at this
    rw [hpos h σ i, hpos h' σ' i] at this
    exact this
  -- the sorting permutation is determined
  set w : Equiv.Perm (Fin j) := σ'⁻¹ * σ with hw
  have hwmono : ∀ a b : Fin j, a.val < b.val → (w a).val < (w b).val := by
    intro a b hab
    have h1 : (h⁻¹ (card n j hj x₀ (σ⁻¹ (σ a)))) = (h'⁻¹ (card n j hj x₀ (σ'⁻¹ (σ a)))) :=
      hkey (σ a)
    have h2 : (h⁻¹ (card n j hj x₀ (σ⁻¹ (σ b)))) = (h'⁻¹ (card n j hj x₀ (σ'⁻¹ (σ b)))) :=
      hkey (σ b)
    have hinv : ∀ a : Fin j, σ⁻¹ (σ a) = a := fun a => (Equiv.Perm.inv_eq_iff_eq).mpr rfl
    rw [hinv a] at h1
    rw [hinv b] at h2
    have h3 := hA a b hab
    rw [h1, h2] at h3
    have hwa : w a = σ'⁻¹ (σ a) := rfl
    have hwb : w b = σ'⁻¹ (σ b) := rfl
    rw [hwa, hwb]
    by_contra hcon
    push_neg at hcon
    rcases Nat.lt_or_ge (σ'⁻¹ (σ b)).val (σ'⁻¹ (σ a)).val with hlt | hge
    · have := hA' _ _ hlt
      omega
    · have heqab : (σ'⁻¹ (σ a)) = (σ'⁻¹ (σ b)) := Fin.ext (by omega)
      have : a = b := by
        have := congrArg (fun x => σ⁻¹ (σ' x)) heqab
        simpa using this
      omega
  have hwid : ∀ i : Fin j, w i = i := strictMono_perm_eq_one w hwmono
  have hσ : σ' = σ := by
    have hone : w = 1 := Equiv.ext hwid
    rw [hw] at hone
    exact inv_mul_eq_one.mp hone
  subst hσ
  have hh : h = h' := by
    have := heq
    simp only [] at this
    exact mul_left_cancel this
  rw [hh]

/-! ### Estimates on the two Lyapunov functions -/

private lemma gfun_lower (n j : ℕ) (hj1 : 1 ≤ j) (hjn : j < n) :
    (n : ℝ) * (Real.log n - Real.log j) ≤ gfun n (n - j) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have htel : ∑ i ∈ Finset.range (n - j),
      (Real.log ((n : ℝ) - (i : ℝ)) - Real.log ((n : ℝ) - ((i : ℝ) + 1)))
      = Real.log (n : ℝ) - Real.log (j : ℝ) := by
    have h := Finset.sum_range_sub' (fun i : ℕ => Real.log ((n : ℝ) - (i : ℝ))) (n - j)
    have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hjn)]
    simp only [Nat.cast_add, Nat.cast_one] at h
    rw [h, hcast]
    norm_num
  have key : ∀ i ∈ Finset.range (n - j),
      (n : ℝ) * (Real.log ((n : ℝ) - (i : ℝ)) - Real.log ((n : ℝ) - ((i : ℝ) + 1)))
        ≤ (n : ℝ) / ((n : ℝ) - ((i : ℝ) + 1)) := by
    intro i hi
    have hir : i < n - j := Finset.mem_range.mp hi
    have h1 : ((i : ℝ) + 1) < (n : ℝ) := by
      have : i + 1 < n := by omega
      exact_mod_cast this
    have hd : (0 : ℝ) < (n : ℝ) - ((i : ℝ) + 1) := by linarith
    have hd2 : (0 : ℝ) < (n : ℝ) - (i : ℝ) := by linarith
    have hlog : Real.log ((n : ℝ) - (i : ℝ)) - Real.log ((n : ℝ) - ((i : ℝ) + 1))
        ≤ 1 / ((n : ℝ) - ((i : ℝ) + 1)) := by
      rw [← Real.log_div (ne_of_gt hd2) (ne_of_gt hd)]
      have := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < ((n : ℝ) - (i : ℝ)) / ((n : ℝ) - ((i : ℝ) + 1)) by positivity)
      have heq : ((n : ℝ) - (i : ℝ)) / ((n : ℝ) - ((i : ℝ) + 1)) - 1
          = 1 / ((n : ℝ) - ((i : ℝ) + 1)) := by
        field_simp
        ring
      linarith [this, heq.le, heq.ge]
    have := mul_le_mul_of_nonneg_left hlog hnR.le
    calc (n : ℝ) * (Real.log ((n : ℝ) - (i : ℝ)) - Real.log ((n : ℝ) - ((i : ℝ) + 1)))
        ≤ (n : ℝ) * (1 / ((n : ℝ) - ((i : ℝ) + 1))) := this
      _ = (n : ℝ) / ((n : ℝ) - ((i : ℝ) + 1)) := by ring
  calc (n : ℝ) * (Real.log (n : ℝ) - Real.log (j : ℝ))
      = ∑ i ∈ Finset.range (n - j),
        (n : ℝ) * (Real.log ((n : ℝ) - (i : ℝ)) - Real.log ((n : ℝ) - ((i : ℝ) + 1))) := by
        rw [← Finset.mul_sum, htel]
    _ ≤ gfun n (n - j) := Finset.sum_le_sum key

private lemma psifun_upper (n j : ℕ) (hj2 : 2 ≤ j) (hjn : j < n) :
    psifun n (n - j) ≤ (n : ℝ) ^ 2 / ((j : ℝ) - 1) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hj1R : (1 : ℝ) < (j : ℝ) := by exact_mod_cast hj2
  have htel : ∑ i ∈ Finset.range (n - j),
      ((1 : ℝ) / ((n : ℝ) - ((i : ℝ) + 1) - 1) - 1 / ((n : ℝ) - (i : ℝ) - 1))
      = 1 / ((j : ℝ) - 1) - 1 / ((n : ℝ) - 1) := by
    have h := Finset.sum_range_sub
      (fun i : ℕ => (1 : ℝ) / ((n : ℝ) - (i : ℝ) - 1)) (n - j)
    have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hjn)]
    simp only [Nat.cast_add, Nat.cast_one] at h
    rw [h, hcast]
    push_cast
    ring
  have key : ∀ i ∈ Finset.range (n - j),
      (n : ℝ) * ((i : ℝ) + 1) / ((n : ℝ) - ((i : ℝ) + 1)) ^ 2
        ≤ (n : ℝ) ^ 2 * ((1 : ℝ) / ((n : ℝ) - ((i : ℝ) + 1) - 1)
            - 1 / ((n : ℝ) - (i : ℝ) - 1)) := by
    intro i hi
    have hir : i < n - j := Finset.mem_range.mp hi
    have h1 : ((i : ℝ) + 1) < (n : ℝ) := by
      have : i + 1 < n := by omega
      exact_mod_cast this
    have h2 : ((i : ℝ) + 2) ≤ (n : ℝ) - 1 := by
      have : i + 2 ≤ n - 1 := by omega
      have h3 : ((i + 2 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega : 1 ≤ n)] at h3
      push_cast at h3
      linarith
    have hb : (0 : ℝ) < (n : ℝ) - ((i : ℝ) + 1) := by linarith
    have hb2 : (0 : ℝ) < (n : ℝ) - ((i : ℝ) + 1) - 1 := by linarith
    have heq : (1 : ℝ) / ((n : ℝ) - ((i : ℝ) + 1) - 1) - 1 / ((n : ℝ) - (i : ℝ) - 1)
        = 1 / (((n : ℝ) - ((i : ℝ) + 1) - 1) * ((n : ℝ) - ((i : ℝ) + 1))) := by
      have h4 : (n : ℝ) - (i : ℝ) - 1 = (n : ℝ) - ((i : ℝ) + 1) := by ring
      rw [h4]
      field_simp
      ring
    rw [heq, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hprod : ((i : ℝ) + 1) * ((n : ℝ) - ((i : ℝ) + 1) - 1)
        ≤ (n : ℝ) * ((n : ℝ) - ((i : ℝ) + 1)) :=
      mul_le_mul h1.le (by linarith) (by linarith) hnR.le
    have hX : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - ((i : ℝ) + 1)) := by positivity
    nlinarith [mul_nonneg hX (sub_nonneg.mpr hprod)]
  calc psifun n (n - j)
      ≤ ∑ i ∈ Finset.range (n - j), (n : ℝ) ^ 2 * ((1 : ℝ) / ((n : ℝ) - ((i : ℝ) + 1) - 1)
          - 1 / ((n : ℝ) - (i : ℝ) - 1)) := Finset.sum_le_sum key
    _ = (n : ℝ) ^ 2 * (1 / ((j : ℝ) - 1) - 1 / ((n : ℝ) - 1)) := by
        rw [← Finset.mul_sum, htel]
    _ ≤ (n : ℝ) ^ 2 / ((j : ℝ) - 1) := by
        have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (n : ℝ) := by
            have : 2 ≤ n := by omega
            exact_mod_cast this
          linarith
        have : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (1 / ((n : ℝ) - 1)) := by positivity
        have hexp : (n : ℝ) ^ 2 * (1 / ((j : ℝ) - 1) - 1 / ((n : ℝ) - 1))
            = (n : ℝ) ^ 2 / ((j : ℝ) - 1) - (n : ℝ) ^ 2 * (1 / ((n : ℝ) - 1)) := by
          ring
        rw [hexp]
        linarith

/-! ### Assembling the lower bound -/

private lemma pos_start (n j : ℕ) (hj : j ≤ n) (hjpos : 0 < j) (x₀ : Equiv.Perm (Fin n)) :
    ((x₀⁻¹ (card n j hj x₀ ⟨0, hjpos⟩)).val) = n - j := by
  simp [card]

private lemma dist_ge (n j : ℕ) (hj2 : 2 ≤ j) (hjn : j < n) (x₀ : Equiv.Perm (Fin n))
    (α : ℝ) (hα : Real.log j < α) (t : ℕ)
    (ht : (t : ℝ) ≤ (n : ℝ) * Real.log n - α * (n : ℝ)) :
    1 - 1 / (((j : ℝ) - 1) * (α - Real.log j) ^ 2) - 1 / (Nat.factorial j : ℝ)
      ≤ distStationary (topToRandom n) (uniformDist (Equiv.Perm (Fin n))) t := by
  classical
  have hn : 0 < n := by omega
  have hj : j ≤ n := le_of_lt hjn
  have hjpos : 0 < j := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hj1R : (1 : ℝ) < (j : ℝ) := by exact_mod_cast hj2
  have hgap : (0 : ℝ) < α - Real.log j := by linarith
  set c₀ : Fin n := card n j hj x₀ ⟨0, hjpos⟩ with hc₀
  have hx0 : x₀ ∉ Sset n c₀ := by
    rw [mem_Sset, hc₀, pos_start]
    omega
  set K : ℝ := gfun n (n - j) with hK
  have hposx : ((x₀⁻¹ c₀).val) = n - j := by rw [hc₀, pos_start]
  have hKlow : (n : ℝ) * (Real.log n - Real.log j) ≤ K := gfun_lower n j (by omega) hjn
  have hKt : (t : ℝ) < K := by
    have h1 : (n : ℝ) * (α - Real.log j) > 0 := by positivity
    nlinarith [hKlow, ht, h1]
  have hcheb := cheb hn x₀ c₀ hx0 t (by rw [hposx, ← hK]; exact hKt)
  rw [hposx] at hcheb
  -- bound the right-hand side
  have hpsi : psifun n (n - j) ≤ (n : ℝ) ^ 2 / ((j : ℝ) - 1) := psifun_upper n j hj2 hjn
  have hDelta : (n : ℝ) * (α - Real.log j) ≤ K - (t : ℝ) := by nlinarith [hKlow, ht]
  have hDpos : (0 : ℝ) < (n : ℝ) * (α - Real.log j) := by positivity
  have hratio : psifun n (n - j) / (K - (t : ℝ)) ^ 2
      ≤ 1 / (((j : ℝ) - 1) * (α - Real.log j) ^ 2) := by
    have h1 : ((n : ℝ) * (α - Real.log j)) ^ 2 ≤ (K - (t : ℝ)) ^ 2 := by nlinarith [hDelta, hDpos]
    have h2 : (0 : ℝ) < ((n : ℝ) * (α - Real.log j)) ^ 2 := by positivity
    calc psifun n (n - j) / (K - (t : ℝ)) ^ 2
        ≤ ((n : ℝ) ^ 2 / ((j : ℝ) - 1)) / ((n : ℝ) * (α - Real.log j)) ^ 2 := by
          refine div_le_div₀ (by positivity) hpsi h2 h1
      _ = 1 / (((j : ℝ) - 1) * (α - Real.log j) ^ 2) := by
          field_simp
          try ring
  -- the surviving mass is inside `Aset`
  have hA := tail_le_A n j hj hjpos x₀ hn t
  rw [← hc₀] at hA
  -- the uniform mass of `Aset` is small
  have hcardpos : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    have : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
    exact_mod_cast this
  have hfacpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by
    have : 0 < Nat.factorial j := Nat.factorial_pos j
    exact_mod_cast this
  have huni : ∑ h ∈ Aset n j hj x₀, uniformDist (Equiv.Perm (Fin n)) h
      ≤ 1 / (Nat.factorial j : ℝ) := by
    have hsum : ∑ h ∈ Aset n j hj x₀, uniformDist (Equiv.Perm (Fin n)) h
        = ((Aset n j hj x₀).card : ℝ) * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ))⁻¹ := by
      simp only [uniformDist]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum, ← div_eq_mul_inv, div_le_div_iff₀ hcardpos hfacpos, one_mul]
    have := Aset_card n j hj x₀
    have hc : ((Aset n j hj x₀).card * Nat.factorial j : ℕ)
        ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℕ) := this
    exact_mod_cast hc
  -- assemble
  have htv : (∑ h ∈ Aset n j hj x₀, rowDist (topToRandom n) t x₀ h)
      - (∑ h ∈ Aset n j hj x₀, uniformDist (Equiv.Perm (Fin n)) h)
      ≤ tvDist (rowDist (topToRandom n) t x₀) (uniformDist (Equiv.Perm (Fin n))) := by
    have hle := le_ciSup (f := fun S : Finset (Equiv.Perm (Fin n)) =>
      |∑ x ∈ S, rowDist (topToRandom n) t x₀ x
        - ∑ x ∈ S, uniformDist (Equiv.Perm (Fin n)) x|)
      (Finite.bddAbove_range _) (Aset n j hj x₀)
    have habs := le_abs_self ((∑ x ∈ Aset n j hj x₀, rowDist (topToRandom n) t x₀ x)
      - ∑ x ∈ Aset n j hj x₀, uniformDist (Equiv.Perm (Fin n)) x)
    simp only [tvDist]
    linarith [hle, habs]
  have hds : tvDist (rowDist (topToRandom n) t x₀) (uniformDist (Equiv.Perm (Fin n)))
      ≤ distStationary (topToRandom n) (uniformDist (Equiv.Perm (Fin n))) t := by
    simp only [distStationary]
    exact le_ciSup (f := fun x : Equiv.Perm (Fin n) =>
      tvDist (rowDist (topToRandom n) t x) (uniformDist (Equiv.Perm (Fin n))))
      (Finite.bddAbove_range _) x₀
  have hrow : (∑ h ∈ Aset n j hj x₀, rowDist (topToRandom n) t x₀ h)
      = ∑ h ∈ Aset n j hj x₀, ((topToRandom n) ^ t) x₀ h := rfl
  rw [hrow] at htv
  linarith [hcheb, hratio, hA, huni, htv, hds]

end TTR

end

end MarkovMixing

open MarkovMixing

open scoped BigOperators

/-- **Proposition 7.14** (LPW): for the top-to-random shuffle on `n` cards,
for every `ε > 0` there is an `α₀` such that for `α > α₀` and all
sufficiently large `n`, `d(n log n − α n) ≥ 1 − ε`. -/
theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, α₀ < α → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : ℕ, (t : ℝ) ≤ n * Real.log n - α * n →
        1 - ε ≤ distStationary (topToRandom n)
          (uniformDist (Equiv.Perm (Fin n))) t := by
  classical
  set j : ℕ := max 2 (⌈2 / ε⌉₊ + 1) with hjdef
  have hj2 : 2 ≤ j := le_max_left _ _
  have hj1R : (1 : ℝ) < (j : ℝ) := by
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
    linarith
  have hfacge : 2 / ε ≤ (Nat.factorial j : ℝ) := by
    have h1 : (2 : ℝ) / ε ≤ (j : ℝ) := by
      have hc : (2 : ℝ) / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈2 / ε⌉₊ + 1 : ℕ) ≤ j := le_max_right _ _
      have h3 : ((⌈2 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h2
      push_cast at h3
      linarith
    have h4 : (j : ℝ) ≤ (Nat.factorial j : ℝ) := by
      exact_mod_cast Nat.self_le_factorial j
    linarith
  have hfacpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by
    have : 0 < Nat.factorial j := Nat.factorial_pos j
    exact_mod_cast this
  have hfacle : 1 / (Nat.factorial j : ℝ) ≤ ε / 2 := by
    rw [div_le_div_iff₀ hfacpos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ hε] at hfacge
    linarith
  set s0 : ℝ := Real.sqrt (2 / (((j : ℝ) - 1) * ε)) with hs0
  have hs0nn : 0 ≤ s0 := Real.sqrt_nonneg _
  set α₀ : ℝ := max 1 (Real.log j + s0) with hα₀
  refine ⟨α₀, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro α hα
  refine ⟨j + 1, ?_⟩
  intro n hn t ht
  have hjn : j < n := by omega
  have hlogj : Real.log j < α := by
    have h1 : Real.log j + s0 ≤ α₀ := le_max_right _ _
    linarith
  have hgap : s0 < α - Real.log j := by
    have h1 : Real.log j + s0 ≤ α₀ := le_max_right _ _
    linarith
  have hsq : 2 / (((j : ℝ) - 1) * ε) < (α - Real.log j) ^ 2 := by
    have hsqr : s0 ^ 2 = 2 / (((j : ℝ) - 1) * ε) :=
      Real.sq_sqrt (by positivity)
    nlinarith [hgap, hs0nn]
  have hprodpos : (0 : ℝ) < ((j : ℝ) - 1) * (α - Real.log j) ^ 2 := by
    have : (0 : ℝ) < α - Real.log j := by linarith
    positivity
  have hterm : 1 / (((j : ℝ) - 1) * (α - Real.log j) ^ 2) ≤ ε / 2 := by
    rw [div_le_div_iff₀ hprodpos (by norm_num : (0 : ℝ) < 2)]
    have h1 : 2 / ε < ((j : ℝ) - 1) * (α - Real.log j) ^ 2 := by
      have hjm : (0 : ℝ) < (j : ℝ) - 1 := by linarith
      have he : ((j : ℝ) - 1) * (2 / (((j : ℝ) - 1) * ε)) = 2 / ε := by
        field_simp
      nlinarith [hsq, hjm]
    rw [div_lt_iff₀ hε] at h1
    linarith
  have hmain := dist_ge n j hj2 hjn 1 α hlogj t ht
  linarith
