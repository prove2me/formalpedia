-- Prove2me | solution 1 for mme_recursive_thin_regional_counts_and_log_rates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T15:45:10.20103+00:00
-- url     : https://prove2.me/submissions/cb3c8bc1-afe8-474c-976c-0e6d28185021

import Theorems.Thm_mme_recursive_thin_split_marginal_joint_counts
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Theorems.Thm_mme_scaled_multinomial_log_rate
import Mathlib.Tactic

open BigOperators Filter MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MME.DWZC1CoarseCounts

theorem prescribed_card {A : Type*} [Fintype A] (n : ℕ) (m : A → ℕ)
    (hm : ∑ a, m a = n) :
    Nat.card {w : Fin n → A // ∀ a, Fintype.card {t // w t = a} = m a} =
      Nat.multinomial Finset.univ m := by
  have h := mme_fintype_prescribed_fiber_function_card (α := Fin n) m
    (by simpa only [Fintype.card_fin] using hm)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.multinomial, hm] using h

theorem joint_card (half : ℕ) (parent : Fin 3 → ℕ) (n : ℕ)
    (m : Split half parent → ℕ) (hm : ∑ a, m a = n) :
    Nat.card {w : Fin n → Split half parent // HasJointCounts w m} =
      Nat.multinomial Finset.univ m := by
  have h := prescribed_card n m hm
  simpa only [HasJointCounts, count, Fintype.card_subtype] using h

theorem target_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) :
    (target (n := n) m).card = ∏ r, Nat.multinomial Finset.univ (m r) := by
  have he := @Equiv.subtypePiEquivPi (Fin R)
    (fun r ↦ Fin (n r) → Split half (parent r))
    (fun r w ↦ HasJointCounts w (m r))
  have hc := Nat.card_congr he
  rw [Nat.card_pi] at hc
  have hcard : (target (n := n) m).card =
      Nat.card {w : Address half R parent n // ∀ r, HasJointCounts (w r) (m r)} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, target]
  rw [hcard, hc]
  exact Finset.prod_congr rfl (fun r _ ↦ joint_card half (parent r) (n r) (m r) (hm r))

def marginal {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) (j : Fin (half + 1)) : ℕ :=
  ∑ a : {a : Split half parent // a.val i = j}, m a.val

theorem marginal_sum {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) :
    (∑ j, marginal m i j) = ∑ a, m a := by
  exact Fintype.sum_fiberwise (fun a : Split half parent ↦ a.val i) m

def degree {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) : ℕ :=
  ∏ j, (marginal m i j).factorial /
    ∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial

theorem joint_fiber_card (half : ℕ) (parent : Fin 3 → ℕ) (n : ℕ)
    (m : Split half parent → ℕ) (i : Fin 3) (x : Fin n → Fin (half + 1))
    (hx : ∀ j, Fintype.card {t // x t = j} = marginal m i j) :
    Nat.card {w : Fin n → Split half parent //
      HasJointCounts w m ∧ (∀ t, (w t).val i = x t)} = degree m i := by
  have h := mme_fintype_constrained_prescribed_fiber_function_card
    x (fun a : Split half parent ↦ a.val i) m (fun j ↦ (hx j).symm)
  have he : {w : Fin n → Split half parent //
      HasJointCounts w m ∧ (∀ t, (w t).val i = x t)} ≃
      {w : Fin n → Split half parent //
        (∀ t, (w t).val i = x t) ∧
          ∀ a, Fintype.card {t // w t = a} = m a} :=
    Equiv.subtypeEquivRight (fun w ↦ by
      simp only [HasJointCounts, count, Fintype.card_subtype, and_comm])
  rw [Nat.card_congr he, h]
  simp only [hx, degree]

theorem target_fiber_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (i : Fin 3) (x : ∀ r, Fin (n r) → Fin (half + 1))
    (hx : ∀ r j, Fintype.card {t // x r t = j} = marginal (m r) i j) :
    ((target (n := n) m).filter (fun w ↦ block i w = x)).card =
      ∏ r, degree (m r) i := by
  let W := {w : Address half R parent n //
    ∀ r, HasJointCounts (w r) (m r) ∧ ∀ t, (w r t).val i = x r t}
  have hc : ((target (n := n) m).filter (fun w ↦ block i w = x)).card = Nat.card W := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, target,
      Finset.filter_filter, W]
    apply congrArg Finset.card
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, hxw⟩ r
      exact ⟨hw r, fun t ↦ congrFun (congrFun hxw r) t⟩
    · intro hw
      exact ⟨fun r ↦ (hw r).1, funext fun r ↦ funext (hw r).2⟩
  have he := @Equiv.subtypePiEquivPi (Fin R)
    (fun r ↦ Fin (n r) → Split half (parent r))
    (fun r w ↦ HasJointCounts w (m r) ∧ ∀ t, (w t).val i = x r t)
  rw [hc, Nat.card_congr he, Nat.card_pi]
  exact Finset.prod_congr rfl (fun r _ ↦
    joint_fiber_card half (parent r) (n r) (m r) i (x r) (hx r))

theorem ambient_fiber_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (i : Fin 3) (a : Address half R parent n) (ha : a ∈ ambient (n := n) m) :
    ((ambient (n := n) m).filter (fun b ↦ block i b = block i a)).card =
      ∏ r, degree (m r) i := by
  have he := (mme_recursive_x_hash_family_counts half R parent n m).2.2 hthin
  rw [he]
  apply target_fiber_card
  intro r j
  have h := (Finset.mem_filter.mp ha).2 r i j
  simpa only [HasMarginalCounts, count, Fintype.card_subtype, block, marginal] using h

theorem degree_pos {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) : 0 < degree m i := by
  apply Finset.prod_pos
  intro j _
  exact Nat.multinomial_pos Finset.univ (fun a : {a : Split half parent // a.val i = j} ↦ m a.val)

theorem degree_factorial_spec {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) :
    (∏ a, (m a).factorial) * degree m i = ∏ j, (marginal m i j).factorial := by
  calc
    _ = (∏ j, ∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial) *
        (∏ j, (marginal m i j).factorial /
          ∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial) := by
      rw [Fintype.prod_fiberwise (fun a : Split half parent ↦ a.val i)
        (fun a ↦ (m a).factorial)]
      rfl
    _ = ∏ j, (∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial) *
        ((marginal m i j).factorial /
          ∏ a : {a : Split half parent // a.val i = j}, (m a.val).factorial) :=
      Finset.prod_mul_distrib.symm
    _ = ∏ j, (marginal m i j).factorial := by
      apply Finset.prod_congr rfl
      intro j _
      exact Nat.mul_div_cancel' (Nat.prod_factorial_dvd_factorial_sum Finset.univ
        (fun a : {a : Split half parent // a.val i = j} ↦ m a.val))

theorem multinomial_eq_marginal_mul_degree {half : ℕ} {parent : Fin 3 → ℕ}
    (m : Split half parent → ℕ) (i : Fin 3) :
    Nat.multinomial Finset.univ m =
      Nat.multinomial Finset.univ (marginal m i) * degree m i := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.prod_factorial_pos Finset.univ m)
  rw [Nat.multinomial_spec]
  calc
    (∑ a, m a).factorial = (∏ j, (marginal m i j).factorial) *
        Nat.multinomial Finset.univ (marginal m i) := by
      rw [Nat.multinomial_spec, marginal_sum]
    _ = (∏ a, (m a).factorial) *
        (Nat.multinomial Finset.univ (marginal m i) * degree m i) := by
      rw [← degree_factorial_spec]
      ring

theorem regional_multinomial_factorization (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    (∏ r, Nat.multinomial Finset.univ (m r)) =
      (∏ r, Nat.multinomial Finset.univ (marginal (m r) i)) * ∏ r, degree (m r) i := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun r _ ↦ multinomial_eq_marginal_mul_degree (m r) i)

theorem ambient_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) :
    (ambient (n := n) m).card = ∏ r, Nat.multinomial Finset.univ (m r) := by
  rw [(mme_recursive_x_hash_family_counts half R parent n m).2.2 hthin]
  exact target_card half R parent n m hm

theorem ambient_image_card (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) (i : Fin 3) :
    ((ambient (n := n) m).image (block i)).card =
      ∏ r, Nat.multinomial Finset.univ (marginal (m r) i) := by
  have hc := Finset.card_eq_sum_card_image (block i) (ambient (n := n) m)
  have hf : (∑ x ∈ (ambient (n := n) m).image (block i),
      ((ambient (n := n) m).filter (fun w ↦ block i w = x)).card) =
      ((ambient (n := n) m).image (block i)).card * ∏ r, degree (m r) i := by
    calc
      _ = ∑ _x ∈ (ambient (n := n) m).image (block i), ∏ r, degree (m r) i := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact ambient_fiber_card half R parent hthin n m i a ha
      _ = _ := by simp
  rw [hf, ambient_card half R parent hthin n m hm,
    regional_multinomial_factorization half R parent m i] at hc
  exact (Nat.eq_of_mul_eq_mul_right
    (Finset.prod_pos (fun r _ ↦ degree_pos (m r) i)) hc).symm

end MME.DWZC1CoarseCounts


open BigOperators Filter MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MME.DWZC1CoarseCounts

noncomputable def entropyMass {A : Type*} [Fintype A] (m : A → ℕ) : ℝ :=
  ((∑ a, m a : ℕ) : ℝ) * Real.log ((∑ a, m a : ℕ) : ℝ) -
    ∑ a, (m a : ℝ) * Real.log (m a : ℝ)

def scaled {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (t : ℕ) (r : Fin R)
    (a : Split half (parent r)) : ℕ := m r a * t

def jointCount {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) : ℕ :=
  ∏ r, Nat.multinomial Finset.univ (m r)

def blockCount {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : ℕ :=
  ∏ r, Nat.multinomial Finset.univ (marginal (m r) i)

def starDegree {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : ℕ := ∏ r, degree (m r) i

noncomputable def jointEntropy {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) : ℝ := ∑ r, entropyMass (m r)

noncomputable def blockEntropy {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : ℝ :=
  ∑ r, entropyMass (marginal (m r) i)

theorem jointCount_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) : 0 < jointCount m :=
  Finset.prod_pos (fun _r _ ↦ Nat.multinomial_pos _ _)

theorem blockCount_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : 0 < blockCount m i :=
  Finset.prod_pos (fun _r _ ↦ Nat.multinomial_pos _ _)

theorem starDegree_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) : 0 < starDegree m i :=
  Finset.prod_pos (fun r _ ↦ degree_pos (m r) i)

theorem jointCount_eq_blockCount_mul_starDegree
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    jointCount m = blockCount m i * starDegree m i :=
  regional_multinomial_factorization half R parent m i

theorem product_scaled_multinomial_rate
    {S : Type*} [Fintype S] {A : S → Type*} [∀ s, Fintype (A s)]
    (m : ∀ s, A s → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log
      (∏ s, (Nat.multinomial Finset.univ (fun a ↦ m s a * t) : ℝ)) / (t : ℝ))
      atTop (𝓝 (∑ s, entropyMass (m s))) := by
  have h := tendsto_finset_sum Finset.univ
    (fun s _ ↦ mme_scaled_multinomial_log_rate (m s))
  convert h using 1
  funext t
  rw [Real.log_prod]
  · exact Finset.sum_div ..
  · intro s _
    exact_mod_cast (Nat.multinomial_pos (s := Finset.univ)
      (f := fun a ↦ m s a * t)).ne'

theorem marginal_scaled {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (t : ℕ) (r : Fin R) (i : Fin 3)
    (j : Fin (half + 1)) :
    marginal (scaled m t r) i j = marginal (m r) i j * t := by
  simp only [marginal, scaled, Finset.sum_mul]

theorem jointCount_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log (jointCount (scaled m t) : ℝ) / (t : ℝ))
      atTop (𝓝 (jointEntropy m)) := by
  simpa only [jointCount, scaled, Nat.cast_prod, jointEntropy] using
    product_scaled_multinomial_rate m

theorem blockCount_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    Tendsto (fun t : ℕ ↦ Real.log (blockCount (scaled m t) i : ℝ) / (t : ℝ))
      atTop (𝓝 (blockEntropy m i)) := by
  have h := product_scaled_multinomial_rate (fun r ↦ marginal (m r) i)
  simpa only [blockCount, Nat.cast_prod, blockEntropy,
    show ∀ t r, marginal (scaled m t r) i = fun j ↦ marginal (m r) i j * t from
      fun t r ↦ funext (marginal_scaled m t r i)] using h

theorem starDegree_log_eq {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    Real.log (starDegree m i : ℝ) =
      Real.log (jointCount m : ℝ) - Real.log (blockCount m i : ℝ) := by
  have h := jointCount_eq_blockCount_mul_starDegree m i
  have hb : (blockCount m i : ℝ) ≠ 0 := by exact_mod_cast (blockCount_pos m i).ne'
  have hd : (starDegree m i : ℝ) ≠ 0 := by exact_mod_cast (starDegree_pos m i).ne'
  rw [h, Nat.cast_mul, Real.log_mul hb hd]
  ring

theorem starDegree_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3) :
    Tendsto (fun t : ℕ ↦ Real.log (starDegree (scaled m t) i : ℝ) / (t : ℝ))
      atTop (𝓝 (jointEntropy m - blockEntropy m i)) := by
  simpa only [starDegree_log_eq, sub_div] using
    (jointCount_log_rate m).sub (blockCount_log_rate m i)

def maxStarDegree {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) : ℕ :=
  max (max (starDegree m 0) (starDegree m 1)) (starDegree m 2)

private theorem log_max_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (max a b) = max (Real.log a) (Real.log b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log ha h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log hb h)]

theorem maxStarDegree_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log (maxStarDegree (scaled m t) : ℝ) / (t : ℝ))
      atTop (𝓝 (max (max (jointEntropy m - blockEntropy m 0)
        (jointEntropy m - blockEntropy m 1)) (jointEntropy m - blockEntropy m 2))) := by
  have h := ((starDegree_log_rate m 0).max (starDegree_log_rate m 1)).max
    (starDegree_log_rate m 2)
  convert h using 1
  funext t
  have hd (i : Fin 3) : (0 : ℝ) < starDegree (scaled m t) i := by
    exact_mod_cast starDegree_pos (scaled m t) i
  rw [maxStarDegree, Nat.cast_max, Nat.cast_max,
    log_max_pos _ _ (lt_max_of_lt_left (hd 0)) (hd 2),
    log_max_pos _ _ (hd 0) (hd 1),
    max_div_div_right (Nat.cast_nonneg t), max_div_div_right (Nat.cast_nonneg t)]

theorem classical_surviving_log_rate {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) :
    Tendsto (fun t : ℕ ↦
      (Real.log (jointCount (scaled m t) : ℝ) -
        Real.log (maxStarDegree (scaled m t) : ℝ)) / (t : ℝ))
      atTop (𝓝 (min (min (blockEntropy m 0) (blockEntropy m 1)) (blockEntropy m 2))) := by
  have h := (jointCount_log_rate m).sub (maxStarDegree_log_rate m)
  have hid : jointEntropy m -
      max (max (jointEntropy m - blockEntropy m 0) (jointEntropy m - blockEntropy m 1))
        (jointEntropy m - blockEntropy m 2) =
      min (min (blockEntropy m 0) (blockEntropy m 1)) (blockEntropy m 2) := by
    simp only [max_def, min_def]
    split_ifs <;> linarith
  simpa only [← sub_div, hid] using h

end MME.DWZC1CoarseCounts

theorem solution
    (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (m : ∀ r, Split half (parent r) → ℕ) :
    let M : Fin R → Fin 3 → Fin (half + 1) → ℕ := fun r i j ↦
      ∑ a : {a : Split half (parent r) // a.val i = j}, m r a.val
    let n : ℕ → Fin R → ℕ := fun t r ↦ (∑ a, m r a) * t
    let mt : ∀ t r, Split half (parent r) → ℕ := fun t r a ↦ m r a * t
    let T : ℕ → ℕ := fun t ↦ ∏ r, Nat.multinomial Finset.univ (mt t r)
    let B : ℕ → Fin 3 → ℕ := fun t i ↦ ∏ r,
      Nat.multinomial Finset.univ (fun j ↦ M r i j * t)
    let Deg : ℕ → Fin 3 → ℕ := fun t i ↦ ∏ r, ∏ j,
      (M r i j * t).factorial /
        ∏ a : {a : Split half (parent r) // a.val i = j}, (mt t r a.val).factorial
    let H : ℝ := ∑ r, (
      ((∑ a, m r a : ℕ) : ℝ) * Real.log ((∑ a, m r a : ℕ) : ℝ) -
        ∑ a, (m r a : ℝ) * Real.log (m r a : ℝ))
    let HM : Fin 3 → ℝ := fun i ↦ ∑ r, (
      ((∑ j, M r i j : ℕ) : ℝ) * Real.log ((∑ j, M r i j : ℕ) : ℝ) -
        ∑ j, (M r i j : ℝ) * Real.log (M r i j : ℝ))
    let maxDeg : ℕ → ℕ := fun t ↦ max (max (Deg t 0) (Deg t 1)) (Deg t 2)
    (∀ t : ℕ,
      ambient (n := n t) (mt t) = target (n := n t) (mt t) ∧
      (target (n := n t) (mt t)).Nonempty ∧
      (ambient (n := n t) (mt t)).card = T t ∧
      ∀ i : Fin 3,
        ((ambient (n := n t) (mt t)).image (block i)).card = B t i ∧
        T t = B t i * Deg t i ∧
        ∀ a ∈ ambient (n := n t) (mt t),
          ((ambient (n := n t) (mt t)).filter (fun b ↦ block i b = block i a)).card =
            Deg t i) ∧
    Tendsto (fun t : ℕ ↦ Real.log (T t : ℝ) / (t : ℝ)) atTop (𝓝 H) ∧
    (∀ i : Fin 3,
      Tendsto (fun t : ℕ ↦ Real.log (B t i : ℝ) / (t : ℝ)) atTop (𝓝 (HM i)) ∧
      Tendsto (fun t : ℕ ↦ Real.log (Deg t i : ℝ) / (t : ℝ)) atTop (𝓝 (H - HM i))) ∧
    Tendsto (fun t : ℕ ↦ Real.log (maxDeg t : ℝ) / (t : ℝ))
      atTop (𝓝 (max (max (H - HM 0) (H - HM 1)) (H - HM 2))) ∧
    Tendsto (fun t : ℕ ↦ (Real.log (T t : ℝ) - Real.log (maxDeg t : ℝ)) / (t : ℝ))
      atTop (𝓝 (min (min (HM 0) (HM 1)) (HM 2))) := by
  dsimp only
  have hn (t : ℕ) (r : Fin R) :
      (∑ a, m r a * t) = (∑ a, m r a) * t := (Finset.sum_mul ..).symm
  constructor
  · intro t
    refine ⟨(mme_recursive_x_hash_family_counts half R parent
      (fun r ↦ (∑ a, m r a) * t) (fun r a ↦ m r a * t)).2.2 hthin, ?_, ?_, ?_⟩
    · apply Finset.card_pos.mp
      rw [MME.DWZC1CoarseCounts.target_card half R parent _ _ (hn t)]
      exact Finset.prod_pos (fun _r _ ↦ Nat.multinomial_pos _ _)
    · exact MME.DWZC1CoarseCounts.ambient_card half R parent hthin _ _ (hn t)
    · intro i
      constructor
      · simpa only [MME.DWZC1CoarseCounts.marginal, Finset.sum_mul] using
          MME.DWZC1CoarseCounts.ambient_image_card half R parent hthin _
            (fun r a ↦ m r a * t) (hn t) i
      constructor
      · simpa only [MME.DWZC1CoarseCounts.marginal,
          MME.DWZC1CoarseCounts.degree, Finset.sum_mul] using
          MME.DWZC1CoarseCounts.regional_multinomial_factorization half R parent
            (fun r a ↦ m r a * t) i
      · intro a ha
        simpa only [MME.DWZC1CoarseCounts.marginal,
          MME.DWZC1CoarseCounts.degree, Finset.sum_mul] using
          MME.DWZC1CoarseCounts.ambient_fiber_card half R parent hthin _
            (fun r a ↦ m r a * t) i a ha
  have ht := MME.DWZC1CoarseCounts.jointCount_log_rate m
  have hb := MME.DWZC1CoarseCounts.blockCount_log_rate m
  have hd := MME.DWZC1CoarseCounts.starDegree_log_rate m
  have hmax := MME.DWZC1CoarseCounts.maxStarDegree_log_rate m
  have hsurv := MME.DWZC1CoarseCounts.classical_surviving_log_rate m
  simpa only [MME.DWZC1CoarseCounts.jointCount, MME.DWZC1CoarseCounts.blockCount,
    MME.DWZC1CoarseCounts.starDegree, MME.DWZC1CoarseCounts.maxStarDegree,
    MME.DWZC1CoarseCounts.scaled, MME.DWZC1CoarseCounts.marginal,
    MME.DWZC1CoarseCounts.degree, MME.DWZC1CoarseCounts.jointEntropy,
    MME.DWZC1CoarseCounts.blockEntropy, MME.DWZC1CoarseCounts.entropyMass,
    Finset.sum_mul] using ⟨ht, (fun i ↦ ⟨hb i, hd i⟩), hmax, hsurv⟩
