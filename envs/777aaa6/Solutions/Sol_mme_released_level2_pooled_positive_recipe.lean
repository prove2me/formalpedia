-- Prove2me | solution 1 for mme_released_level2_pooled_positive_recipe
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T03:14:34.658584+00:00
-- url     : https://prove2.me/submissions/d3483bee-778e-4706-bbc3-f37e77902058

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
import Theorems.Thm_mme_graded_band_part_stage
import Theorems.Thm_mme_released_recursive_stage_level2_rate_margin
import Theorems.Thm_mme_exact_profile_boundary_end
import Theorems.Thm_mme_log_joint_recipe_g_stage_compose
import Theorems.Thm_mme_rational_log_series_certificate
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace C7L2
open RecStage

theorem l2_data : ∀ r : Fin 1104, 0 < (l2At r).2.1 ∧ (l2At r).2.2 ≤ D / 2 ∧
    ((l2At r).1 = (1, 1, 2) ∨ (l2At r).1 = (1, 2, 1) ∨ (l2At r).1 = (2, 1, 1)) := by
  decide +kernel

theorem parent2_cases (r : Fin 1104) :
    parent2 r = ![1, 1, 2] ∨ parent2 r = ![1, 2, 1] ∨ parent2 r = ![2, 1, 1] := by
  obtain ⟨-, -, h⟩ := l2_data r
  unfold parent2
  rcases h with h | h | h <;> rw [h]
  · left; decide
  · right; left; decide
  · right; right; decide

theorem D_eq : D = 1000000000000 := rfl

/-- On a positive shape, `jw` is `s0` exactly when the doubled coordinate `k` of the shape
is split as `2 + 0` or `0 + 2`, and `D/2 - s0` otherwise. -/
theorem jw_sum (p : Fin 3 → ℕ)
    (hp : p = ![1, 1, 2] ∨ p = ![1, 2, 1] ∨ p = ![2, 1, 1]) (s0 : ℕ) (hs : s0 ≤ D / 2) :
    ∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) p,
      jw (p 0) (p 1) (p 2) s0 (e.val 0).val (e.val 1).val (e.val 2).val = D := by
  have hD := D_eq
  rcases hp with rfl | rfl | rfl
  · have key : ∀ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) ![1, 1, 2],
        jw (![1, 1, 2] 0) (![1, 1, 2] 1) (![1, 1, 2] 2) s0 (e.val 0).val (e.val 1).val (e.val 2).val =
          if (e.val 2).val = 2 ∨ (e.val 2).val = 0 then s0 else D / 2 - s0 := by
      rintro ⟨v, hv1, hv2⟩
      have h0 := hv2 0; have h1 := hv2 1; have h2 := hv2 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 ⊢
      simp only [jw]
      split_ifs <;> first | omega | simp_all
    rw [Finset.sum_congr rfl (fun e _ ↦ key e), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul]
    have c1 : (Finset.univ.filter (fun e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) ![1, 1, 2] ↦
      (e.val 2).val = 2 ∨ (e.val 2).val = 0)).card = 2 := by decide
    have c2 : (Finset.univ.filter (fun e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) ![1, 1, 2] ↦
      ¬ ((e.val 2).val = 2 ∨ (e.val 2).val = 0))).card = 2 := by decide
    rw [c1, c2]; rw [hD] at hs ⊢; omega
  · have key : ∀ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) ![1, 2, 1],
        jw (![1, 2, 1] 0) (![1, 2, 1] 1) (![1, 2, 1] 2) s0 (e.val 0).val (e.val 1).val (e.val 2).val =
          if (e.val 1).val = 2 ∨ (e.val 1).val = 0 then s0 else D / 2 - s0 := by
      rintro ⟨v, hv1, hv2⟩
      have h0 := hv2 0; have h1 := hv2 1; have h2 := hv2 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 ⊢
      simp only [jw]
      split_ifs <;> first | omega | simp_all
    rw [Finset.sum_congr rfl (fun e _ ↦ key e), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul]
    have c1 : (Finset.univ.filter (fun e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) ![1, 2, 1] ↦
      (e.val 1).val = 2 ∨ (e.val 1).val = 0)).card = 2 := by decide
    have c2 : (Finset.univ.filter (fun e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) ![1, 2, 1] ↦
      ¬ ((e.val 1).val = 2 ∨ (e.val 1).val = 0))).card = 2 := by decide
    rw [c1, c2]; rw [hD] at hs ⊢; omega
  · have key : ∀ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) ![2, 1, 1],
        jw (![2, 1, 1] 0) (![2, 1, 1] 1) (![2, 1, 1] 2) s0 (e.val 0).val (e.val 1).val (e.val 2).val =
          if (e.val 0).val = 2 ∨ (e.val 0).val = 0 then s0 else D / 2 - s0 := by
      rintro ⟨v, hv1, hv2⟩
      have h0 := hv2 0; have h1 := hv2 1; have h2 := hv2 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 ⊢
      simp only [jw]
      split_ifs <;> first | omega | simp_all
    rw [Finset.sum_congr rfl (fun e _ ↦ key e), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul]
    have c1 : (Finset.univ.filter (fun e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) ![2, 1, 1] ↦
      (e.val 0).val = 2 ∨ (e.val 0).val = 0)).card = 2 := by decide
    have c2 : (Finset.univ.filter (fun e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) ![2, 1, 1] ↦
      ¬ ((e.val 0).val = 2 ∨ (e.val 0).val = 0))).card = 2 := by decide
    rw [c1, c2]; rw [hD] at hs ⊢; omega

theorem m2_sum (r : Fin 1104) : ∑ c, m2 r c = n2 r := by
  obtain ⟨-, hs, -⟩ := l2_data r
  simp only [m2, n2]
  rw [← Finset.sum_mul, ← Finset.mul_sum, jw_sum _ (parent2_cases r) _ hs]
  ring


theorem exists_word {α : Type} [Fintype α] [DecidableEq α] (m : α → ℕ) (n : ℕ)
    (h : ∑ a, m a = n) : ∃ w : Fin n → α, ∀ a, RecursiveThinSplit.count w a = m a := by
  subst h
  have hc : Fintype.card ((a : α) × Fin (m a)) = ∑ a, m a := by simp
  let e : Fin (∑ a, m a) ≃ ((a : α) × Fin (m a)) := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun i ↦ (e i).1, fun a ↦ ?_⟩
  unfold RecursiveThinSplit.count
  rw [← Fintype.card_subtype]
  calc Fintype.card {j : Fin (∑ a, m a) // (e j).1 = a}
      = Fintype.card {p : (b : α) × Fin (m b) // p.1 = a} :=
        Fintype.card_congr (e.subtypeEquiv (fun _ ↦ Iff.rfl))
    _ = Fintype.card (Fin (m a)) := by
        refine Fintype.card_congr
          { toFun := fun p ↦ Fin.cast (by rw [p.2]) p.1.2
            invFun := fun q ↦ ⟨⟨a, q⟩, rfl⟩
            left_inv := ?_
            right_inv := fun q ↦ rfl }
        rintro ⟨⟨b, q⟩, hb⟩
        simp only at hb
        subst hb
        rfl
    _ = m a := Fintype.card_fin _

/-- Number of positions of a given full cell. -/
theorem card_fullCell {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : RecursiveXHash.Address half R parent n) (r : Fin R)
    (e : RecursiveThinSplit.Split half (parent r)) :
    Fintype.card {p : Position n // fullCell htotal a p = ⟨r, e⟩} =
      RecursiveThinSplit.count (a r) e +
        RecursiveThinSplit.count (a r) (complement (htotal r) e) := by
  classical
  unfold RecursiveThinSplit.count
  rw [Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single r]
  · rw [Fintype.sum_prod_type]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ ↦ ?_)
    rw [Fin.sum_univ_two]
    simp only [fullCell, Fin.isValue, if_true, one_ne_zero, if_false, Sigma.mk.inj_iff, heq_eq_eq,
      true_and]
    congr 1
    by_cases h : a r t = complement (htotal r) e
    · rw [if_pos h, if_pos (by rw [h, complement_complement])]
    · rw [if_neg h, if_neg (fun h' ↦ h (by rw [← h', complement_complement]))]
  · intro b _ hb
    refine Finset.sum_eq_zero (fun q _ ↦ ?_)
    rw [if_neg]
    intro h
    exact hb (congrArg Sigma.fst h)
  · intro h; exact absurd (Finset.mem_univ r) h

theorem types_pos {M lower : ℕ} {S T : ProfiledCW.Predicate M} (D : LogPartStageG M lower S T)
    (x : Fin 3 → ProfiledCW.FineWord M) (hx : ProfiledCW.supported x) (hT : ∀ i, T i (x i)) :
    1 ≤ D.types := by
  induction D generalizing x with
  | step types rate _ steps _ _ cover =>
      obtain ⟨j, -⟩ := cover x hx hT
      exact Nat.one_le_iff_ne_zero.mpr (fun h ↦ by subst h; exact j.elim0)
  | rotate child ih =>
      apply ih (fun i ↦ x (cyclicPerm i))
      · intro r
        have := hx r
        have hs := Equiv.sum_comp cyclicPerm (fun i ↦ (x i r).val)
        simp only [Fin.sum_univ_three] at hs
        simp only
        omega
      · intro i
        have := hT (cyclicPerm i)
        simpa using this
  | swap child ih =>
      apply ih (fun i ↦ x (swapFirstTwoPerm i))
      · intro r
        have := hx r
        have hs := Equiv.sum_comp swapFirstTwoPerm (fun i ↦ (x i r).val)
        simp only [Fin.sum_univ_three] at hs
        simp only
        omega
      · intro i
        have := hT (swapFirstTwoPerm i)
        simpa using this


open RecStage in
theorem mu2_mass (i : Fin 3) (c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2) :
    ∑ w, mu2 i c w = m2 c.1 c.2 + m2 c.1 (complement (htotal2 c.1) c.2) := by
  unfold mu2
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have : (Finset.univ.filter (fun w : CompleteSplit.CompleteWord 1 ↦
      (w 0).val = (c.2.val i).val)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨fun _ ↦ ⟨(c.2.val i).val, by have := (c.2.val i).isLt; omega⟩, ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext r; apply Fin.ext
      have hr : r = 0 := Fin.ext (by have := r.isLt; norm_num at this; omega)
      subst hr; exact h
    · intro h; subst h; rfl
  rw [this, one_mul]

/-- The zero mode chosen for a level-1 cell, and the letter it forces in the next mode. -/
def zmode (e : Fin 3 → ℕ) : Fin 3 := if e 0 = 0 then 0 else if e 1 = 0 then 1 else 2

def nextLetter (e : Fin 3 → ℕ) : ℕ := if e 0 = 0 then e 1 else if e 1 = 0 then e 2 else e 0

theorem nextLetter_eq (e : Fin 3 → ℕ) : e (zmode e + 1) = nextLetter e := by
  unfold zmode nextLetter
  split_ifs <;> rfl

theorem ones_pointwise (p : Fin 3 → ℕ)
    (hp : p = ![1, 1, 2] ∨ p = ![1, 2, 1] ∨ p = ![2, 1, 1]) (s0 : ℕ) (hs : s0 ≤ D / 2)
    (x0 x1 x2 : ℕ) (hx : x0 + x1 + x2 = 2) (h0 : x0 ≤ p 0) (h1 : x1 ≤ p 1) (h2 : x2 ≤ p 2) :
    (jw (p 0) (p 1) (p 2) s0 x0 x1 x2 + jw (p 0) (p 1) (p 2) s0 (p 0 - x0) (p 1 - x1) (p 2 - x2)) *
      (if nextLetter ![x0, x1, x2] = 1 then 1 else 0) =
    (if (x0 = 1 ∧ x1 = 1) ∨ (x0 = 1 ∧ x2 = 1) ∨ (x1 = 1 ∧ x2 = 1) then
      (if x0 = 2 ∨ x1 = 2 ∨ x2 = 2 ∨ p 0 - x0 = 2 ∨ p 1 - x1 = 2 ∨ p 2 - x2 = 2
        then 2 * s0 else 2 * (D / 2 - s0)) else 0) := by
  have hx2 : x2 = 2 - x0 - x1 := by omega
  subst hx2
  have hD := D_eq
  rcases hp with rfl | rfl | rfl <;>
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 ⊢
    interval_cases x0 <;> interval_cases x1 <;>
      simp (config := {decide := true}) [jw, nextLetter] <;> omega

theorem ite_split (C C' : Prop) [Decidable C] [Decidable C'] (a b : ℕ) :
    (if C then (if C' then a else b) else 0) =
      (if C ∧ C' then a else 0) + (if C ∧ ¬ C' then b else 0) := by
  by_cases hC : C <;> by_cases hC' : C' <;> simp [hC, hC']

theorem ones_sum_gen (p : Fin 3 → ℕ)
    (hp : p = ![1, 1, 2] ∨ p = ![1, 2, 1] ∨ p = ![2, 1, 1])
    (ht : p 0 + p 1 + p 2 = 2 * (2 * 2 ^ (1 - 1))) (s0 : ℕ) (hs : s0 ≤ D / 2) :
    ∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) p,
      (jw (p 0) (p 1) (p 2) s0 (e.val 0).val (e.val 1).val (e.val 2).val +
        jw (p 0) (p 1) (p 2) s0 ((complement ht e).val 0).val ((complement ht e).val 1).val
          ((complement ht e).val 2).val) *
        (if nextLetter (fun i ↦ (e.val i).val) = 1 then 1 else 0) = 2 * (D - s0) := by
  have hD := D_eq
  have key : ∀ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) p,
      (jw (p 0) (p 1) (p 2) s0 (e.val 0).val (e.val 1).val (e.val 2).val +
        jw (p 0) (p 1) (p 2) s0 ((complement ht e).val 0).val ((complement ht e).val 1).val
          ((complement ht e).val 2).val) *
        (if nextLetter (fun i ↦ (e.val i).val) = 1 then 1 else 0) =
      (if ((((e.val 0).val = 1 ∧ (e.val 1).val = 1) ∨ ((e.val 0).val = 1 ∧ (e.val 2).val = 1) ∨
          ((e.val 1).val = 1 ∧ (e.val 2).val = 1)) ∧
          ((e.val 0).val = 2 ∨ (e.val 1).val = 2 ∨ (e.val 2).val = 2 ∨ p 0 - (e.val 0).val = 2 ∨
            p 1 - (e.val 1).val = 2 ∨ p 2 - (e.val 2).val = 2)) then 2 * s0 else 0) +
      (if ((((e.val 0).val = 1 ∧ (e.val 1).val = 1) ∨ ((e.val 0).val = 1 ∧ (e.val 2).val = 1) ∨
          ((e.val 1).val = 1 ∧ (e.val 2).val = 1)) ∧
          ¬ ((e.val 0).val = 2 ∨ (e.val 1).val = 2 ∨ (e.val 2).val = 2 ∨ p 0 - (e.val 0).val = 2 ∨
            p 1 - (e.val 1).val = 2 ∨ p 2 - (e.val 2).val = 2)) then 2 * (D / 2 - s0) else 0) := by
    intro e
    have hn : nextLetter (fun i ↦ (e.val i).val) =
        nextLetter ![(e.val 0).val, (e.val 1).val, (e.val 2).val] := by
      simp [nextLetter]
    have hc : ∀ i, ((complement ht e).val i).val = p i - (e.val i).val := fun _ ↦ rfl
    rw [hn, hc 0, hc 1, hc 2,
      ones_pointwise p hp s0 hs _ _ _ e.2.1 (e.2.2 0) (e.2.2 1) (e.2.2 2)]
    exact ite_split _ _ _ _
  rw [Finset.sum_congr rfl (fun e _ ↦ key e), Finset.sum_add_distrib, Finset.sum_ite,
    Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const_zero, add_zero, add_zero,
    Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  rcases hp with rfl | rfl | rfl
  · rw [show (Finset.univ.filter _).card = 1 from by decide,
      show (Finset.univ.filter _).card = 2 from by decide]
    rw [hD] at hs ⊢; omega
  · rw [show (Finset.univ.filter _).card = 1 from by decide,
      show (Finset.univ.filter _).card = 2 from by decide]
    rw [hD] at hs ⊢; omega
  · rw [show (Finset.univ.filter _).card = 1 from by decide,
      show (Finset.univ.filter _).card = 2 from by decide]
    rw [hD] at hs ⊢; omega

open RecStage in
theorem ones_sum (r : Fin 1104) :
    ∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      (m2 r e + m2 r (complement (htotal2 r) e)) *
        (if nextLetter (fun i ↦ (e.val i).val) = 1 then 1 else 0) =
      2 * D * (l2At r).2.1 * (D - (l2At r).2.2) := by
  obtain ⟨-, hs, -⟩ := l2_data r
  have h := ones_sum_gen (parent2 r) (parent2_cases r) (htotal2 r) _ hs
  simp only [m2]
  calc _ = ∑ e : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
        ((l2At r).2.1 * D) * ((jw (parent2 r 0) (parent2 r 1) (parent2 r 2) (l2At r).2.2
          (e.val 0).val (e.val 1).val (e.val 2).val +
        jw (parent2 r 0) (parent2 r 1) (parent2 r 2) (l2At r).2.2
          ((complement (htotal2 r) e).val 0).val ((complement (htotal2 r) e).val 1).val
          ((complement (htotal2 r) e).val 2).val) *
        (if nextLetter (fun i ↦ (e.val i).val) = 1 then 1 else 0)) := by
          refine Finset.sum_congr rfl (fun e _ ↦ ?_); ring
    _ = _ := by rw [← Finset.mul_sum, h]; ring

theorem Uval_eq : ∑ r : Fin 1104, 2 * RecStage.D * (RecStage.l2At r).2.1 *
    (RecStage.D - (RecStage.l2At r).2.2) =
      13968264640400080378170674914282801769793717486676000000000000 := by
  decide +kernel

theorem log5_lower_gen (L : ℚ) (h : let q : ℚ := 5
    let k : ℤ := -2
    let n := 14
    let t := ((2 : ℚ) ^ k * q - 1) / ((2 : ℚ) ^ k * q + 1)
    let twoCenter := 2 * ∑ i ∈ Finset.range n, (1 / 3 : ℚ) ^ (2 * i + 1) / (2 * i + 1)
    let twoError := 2 * ((1 / 3 : ℚ) ^ (2 * n + 1) / (1 - (1 / 3 : ℚ) ^ 2))
    let center := (2 * ∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * i + 1)) -
      (k : ℚ) * twoCenter
    let error := 2 * (|t| ^ (2 * n + 1) / (1 - t ^ 2)) + |(k : ℚ)| * twoError
    L ≤ center - error ∧ center + error ≤ 2) : (L : ℝ) ≤ Real.log 5 := by
  have := (mme_rational_log_series_certificate 5 (by norm_num) (-2) 14 L 2 h.1 h.2).1
  simpa using this

theorem log5_lower : (160943790 / 100000000 : ℝ) ≤ Real.log 5 := by
  have := log5_lower_gen (160943790 / 100000000) (by decide +kernel)
  simpa using this

/-- One-part position family. -/
def onePart (N : ℕ) : ((j : Fin 1) × Fin ((fun _ : Fin 1 ↦ N) j)) ≃ Fin N where
  toFun p := p.2
  invFun q := ⟨0, q⟩
  left_inv := by rintro ⟨j, q⟩; fin_cases j; rfl
  right_inv _ := rfl

theorem card_position (n : Fin 1104 → ℕ) (t : ℕ) :
    Fintype.card (Position (fun r ↦ t * n r)) = t * ∑ r, n r * 2 := by
  rw [Fintype.card_congr (DWZProfiledRegional.positionsAt n t).symm, Fintype.card_fin]
  simp only [DWZProfiledRegional.lenAt, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ ↦ ?_); ring

theorem bernoulli_nat (t A : ℕ) : t * A + 1 ≤ (t + 1) ^ A := by
  induction A with
  | zero => simp
  | succ A ih =>
      rw [pow_succ]
      nlinarith [Nat.one_le_pow A (t + 1) (Nat.succ_pos t)]

/-- Dimension product of a boundary whose profiles are concentrated on one word per cell. -/
theorem concentrated_dims {K : ℕ} (card : Fin K → ℕ) (w : Fin K → CompleteSplit.CompleteWord 1) :
    ∏ j, ((card j).factorial /
        ∏ s, (if s = w j then card j else 0).factorial) *
      5 ^ (∑ s, (if s = w j then card j else 0) * Boundary.ones s) =
    5 ^ (∑ j, card j * Boundary.ones (w j)) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun j _ ↦ ?_)
  have h1 : ∏ s, (if s = w j then card j else 0).factorial = (card j).factorial := by
    rw [Finset.prod_congr rfl (fun s _ ↦ (apply_ite Nat.factorial (s = w j) (card j) 0))]
    simp [Nat.factorial_zero]
  have h2 : ∑ s, (if s = w j then card j else 0) * Boundary.ones s = card j * Boundary.ones (w j) := by
    rw [Finset.sum_congr rfl (fun s _ ↦ (ite_mul (s = w j) (card j) 0 (Boundary.ones s)))]
    simp
  rw [h1, h2, Nat.div_self (Nat.factorial_pos _), one_mul]

theorem ones_const (x : Fin 3) :
    Boundary.ones (fun _ : Fin (2 ^ (1 - 1)) ↦ x) = if x.val = 1 then 1 else 0 := by
  unfold Boundary.ones
  by_cases h : x.val = 1
  · have hx : x = 1 := Fin.ext h
    rw [if_pos h, hx]; simp
  · rw [if_neg h]
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
    intro _ hx; exact h (by rw [hx]; rfl)

theorem grade_const (x : Fin 3) :
    CWCells.grade (fun _ : Fin (2 ^ (1 - 1)) ↦ x) = x.val := by
  simp [CWCells.grade]

theorem grade1 (w : CompleteSplit.CompleteWord 1) : CWCells.grade w = (w 0).val := by
  unfold CWCells.grade
  rw [Fintype.sum_eq_single 0]
  intro r hr
  exact absurd (Fin.ext (by have := r.isLt; norm_num at this; omega)) hr

theorem word1_ext (u v : CompleteSplit.CompleteWord 1) (h : (u 0).val = (v 0).val) : u = v := by
  funext r
  have hr : r = 0 := Fin.ext (by have := r.isLt; norm_num at this; omega)
  subst hr; exact Fin.ext h

end C7L2

open Filter RecStage DWZProfiledRegional C7L2 in
theorem solution :
    ∃ C : ℕ, ∀ᶠ t : ℕ in atTop,
      ∃ R : LogJointRecipeG (lenAt RecStage.n2 t * 2 ^ (1 - 1)) 2 (fun i x ↦
          ParentGraded RecStage.parent2 (fun r ↦ t * RecStage.n2 r) i
            (ProfiledCW.split (ell := 1) (positionsAt RecStage.n2 t) rfl x) ∧
          parentTypical RecStage.htotal2 (fun r ↦ t * RecStage.n2 r)
            (fun r c ↦ t * RecStage.m2 r c) (fun c w ↦ t * RecStage.mu2 i c w)
            (Real.sqrt (8 * (25 * (1104 : ℝ) *
              (Fintype.card (CompleteSplit.CompleteWord 1) : ℝ) ^ 2) *
              ((Nat.sqrt t + 2 : ℕ) : ℝ) / t))
            (ProfiledCW.split (ell := 1) (positionsAt RecStage.n2 t) rfl x)),
        1 ≤ R.inputs ∧ R.inputs ≤ (t + 1) ^ C ∧ 1 ≤ R.a * R.b * R.c ∧
        ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) * t ≤ R.logOutputs ∧
        ((37468424 * 6 * 10 ^ 53 : ℕ) : ℝ) * t ≤ Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by
  classical
  have hn : ∀ r, 0 < n2 r := fun r ↦ by
    obtain ⟨h, -, -⟩ := l2_data r
    exact Nat.mul_pos h (pow_pos (by rw [D_eq]; norm_num) 2)
  obtain ⟨η, hη, hev⟩ := mme_graded_band_part_stage (ell := 1) parent2 htotal2 n2 hn
    (by norm_num) m2 m2_sum mu2 mu2_mass ((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ)
    (Nat.cast_nonneg _) mme_released_recursive_stage_level2_rate_margin
  set A : ℕ := ∑ r, n2 r * 2 with hA
  set Y : ℕ := 3 * Fintype.card (Cell (2 * 2 ^ (1 - 1)) 1104 parent2) *
    Fintype.card (CompleteSplit.CompleteWord 1) with hY
  refine ⟨A * Y, ?_⟩
  filter_upwards [hev] with t ht
  -- a target address
  have hex : ∀ r, ∃ w : Fin (t * n2 r) → RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r),
      ∀ e, RecursiveThinSplit.count w e = t * m2 r e := fun r ↦
    exists_word _ _ (by rw [← Finset.mul_sum, m2_sum])
  choose a ha using hex
  have ha' : a ∈ RecursiveXHash.target (n := fun r ↦ t * n2 r) (fun r c ↦ t * m2 r c) := by
    unfold RecursiveXHash.target
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun r ↦ ha r
  have hcell : ∀ c : Cell (2 * 2 ^ (1 - 1)) 1104 parent2,
      Fintype.card {p : Position (fun r ↦ t * n2 r) // fullCell htotal2 a p = c} =
        t * m2 c.1 c.2 + t * m2 c.1 (complement (htotal2 c.1) c.2) := by
    rintro ⟨r, e⟩
    rw [card_fullCell, ha, ha]
  -- the stage target
  let T : ProfiledCW.Predicate (lenAt n2 t * 2 ^ (1 - 1)) := fun i y ↦
    Graded htotal2 i a (ProfiledCW.split (ell := 1) (positionsAt n2 t) rfl y) ∧
      count (fullCell htotal2 a) (ProfiledCW.split (ell := 1) (positionsAt n2 t) rfl y) =
        fun c w ↦ t * mu2 i c w
  -- level-1 cells
  let K := Fintype.card (Cell (2 * 2 ^ (1 - 1)) 1104 parent2)
  let ci := Fintype.equivFin (Cell (2 * 2 ^ (1 - 1)) 1104 parent2)
  let cellF : Fin (lenAt n2 t) → Fin K := fun q ↦ ci (fullCell htotal2 a (positionsAt n2 t q))
  let grd : Fin K → Fin 3 → ℕ := fun j i ↦ ((ci.symm j).2.val i).val
  let zero : Fin K → Fin 3 := fun j ↦ zmode (grd j)
  have htot : ∀ j, grd j 0 + grd j 1 + grd j 2 = 2 * 2 ^ (1 - 1) :=
    fun j ↦ (ci.symm j).2.property.1
  have hzero : ∀ j, grd j (zero j) = 0 := by
    intro j
    have := htot j
    simp only [zero, zmode]
    split_ifs with h0 h1
    · exact h0
    · exact h1
    · norm_num at this; omega
  have hlt : ∀ j i, grd j i < 3 := fun j i ↦ ((ci.symm j).2.val i).isLt
  let wd : Fin K → CompleteSplit.CompleteWord 1 := fun j _ ↦ ⟨grd j (zero j + 1), hlt _ _⟩
  let cnt : Fin K → CompleteSplit.CompleteWord 1 → ℕ := fun j s ↦
    if s = wd j then Fintype.card {p : Fin (lenAt n2 t) // cellF p = j} else 0
  have hcount : ∀ j, ∑ s, cnt j s = Fintype.card {p : Fin (lenAt n2 t) // cellF p = j} := by
    intro j; simp [cnt]
  have hsupport : ∀ j s, cnt j s ≠ 0 → CWCells.grade s = grd j (zero j + 1) := by
    intro j s h
    simp only [cnt] at h
    split_ifs at h with hs
    · subst hs; exact grade_const _
    · exact absurd rfl h
  obtain ⟨B, hB⟩ := mme_exact_profile_boundary_end (ell := 1) (N := lenAt n2 t * 2 ^ (1 - 1))
    (L := lenAt n2 t) rfl cellF zero grd htot hzero cnt hcount hsupport
  -- grades force the level-1 words, hence the stage target
  have gradeT : ∀ i (x : ProfiledCW.FineWord (lenAt n2 t * 2 ^ (1 - 1))),
      (∀ q, CWCells.grade (ProfiledCW.split (Equiv.refl (Fin (lenAt n2 t))) rfl x q) =
        grd (cellF q) i) → T i x := by
    intro i x h
    have hf : ∀ p, ProfiledCW.split (ell := 1) (positionsAt n2 t) rfl x p =
        fun _ ↦ ⟨((fullCell htotal2 a p).2.val i).val, ((fullCell htotal2 a p).2.val i).isLt⟩ := by
      intro p
      have h1 := h ((positionsAt n2 t).symm p)
      have e1 : grd (cellF ((positionsAt n2 t).symm p)) i = ((fullCell htotal2 a p).2.val i).val := by
        show ((ci.symm (ci (fullCell htotal2 a ((positionsAt n2 t) ((positionsAt n2 t).symm p))))).2.val i).val = _
        rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      have e2 : ProfiledCW.split (Equiv.refl (Fin (lenAt n2 t))) rfl x ((positionsAt n2 t).symm p) =
          ProfiledCW.split (ell := 1) (positionsAt n2 t) rfl x p := rfl
      rw [e1, e2, grade1] at h1
      apply word1_ext
      exact h1
    refine ⟨fun p ↦ ?_, ?_⟩
    · rw [hf p]; exact grade_const _
    · funext c w
      unfold RecursiveYZ.count
      by_cases hw : (w 0).val = (c.2.val i).val
      · have hmu : mu2 i c w = m2 c.1 c.2 + m2 c.1 (complement (htotal2 c.1) c.2) := by
          simp [mu2, hw]
        rw [hmu, mul_add, ← hcell c, Fintype.card_subtype]
        have hfil : ∀ p ∈ (Finset.univ : Finset (Position (fun r ↦ t * n2 r))),
            (fullCell htotal2 a p = c ∧
              ProfiledCW.split (ell := 1) (positionsAt n2 t) rfl x p = w ↔
              fullCell htotal2 a p = c) := by
          intro p _
          refine ⟨fun h ↦ h.1, fun hp ↦ ⟨hp, ?_⟩⟩
          rw [hf p]
          apply word1_ext
          rw [hp]; exact hw.symm
        apply congrArg Finset.card
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hfil p (Finset.mem_univ _)
      · have hmu : mu2 i c w = 0 := by simp [mu2, hw]
        rw [hmu, mul_zero, Finset.card_eq_zero]
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        simp only [Finset.mem_filter] at hp
        obtain ⟨-, hp, hpw⟩ := hp
        apply hw
        rw [← hpw, hf p, hp]
  -- a supported word satisfying the target, so the stage has a type
  let xs : Fin 3 → ProfiledCW.FineWord (lenAt n2 t * 2 ^ (1 - 1)) := fun i m ↦
    ⟨grd (cellF (finProdFinEquiv.symm m).1) i, hlt _ _⟩
  have xs_grade : ∀ i q, CWCells.grade
      (ProfiledCW.split (Equiv.refl (Fin (lenAt n2 t))) rfl (xs i) q) = grd (cellF q) i := by
    intro i q
    have : ProfiledCW.split (Equiv.refl (Fin (lenAt n2 t))) rfl (xs i) q =
        fun _ ↦ ⟨grd (cellF q) i, hlt _ _⟩ := by
      funext r
      show (⟨grd (cellF (finProdFinEquiv.symm (finProdFinEquiv (q, r))).1) i, hlt _ _⟩ : Fin 3) = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact grade_const _
  have xs_supp : ProfiledCW.supported xs := by
    intro m
    have := htot (cellF (finProdFinEquiv.symm m).1)
    simp only [xs]
    norm_num at this ⊢
    exact this
  -- the band part stage
  let S : ProfiledCW.Predicate (lenAt n2 t * 2 ^ (1 - 1)) := fun i x ↦
    ParentGraded parent2 (fun r ↦ t * n2 r) i
      (ProfiledCW.split (ell := 1) (positionsAt n2 t) rfl x) ∧
    parentTypical htotal2 (fun r ↦ t * n2 r) (fun r c ↦ t * m2 r c) (fun c w ↦ t * mu2 i c w)
      (Real.sqrt (8 * (25 * (1104 : ℝ) *
        (Fintype.card (CompleteSplit.CompleteWord 1) : ℝ) ^ 2) *
        ((Nat.sqrt t + 2 : ℕ) : ℝ) / t))
      (ProfiledCW.split (ell := 1) (positionsAt n2 t) rfl x)
  obtain ⟨Dst, hDtypes, hDrate⟩ := ht a ha' (fun i mu'' ↦ mu'' = fun c w ↦ t * mu2 i c w)
    (by
      rintro i mu'' rfl
      refine ⟨fun c ↦ rfl, fun c w ↦ ?_⟩
      simp only [sub_self, abs_zero]
      exact mul_nonneg hη.le (Nat.cast_nonneg _))
    S
    (by
      intro mu' hmu i x h1 h2
      rw [hmu i] at h2
      refine ⟨h1, ?_⟩
      simpa using h2)
  have hDpos : 1 ≤ Dst.types := types_pos Dst xs xs_supp (fun i ↦ gradeT i (xs i) (xs_grade i))
  -- compose the stage with the boundary
  obtain ⟨R, hR1, hRX, hRrate, hRa, hRb, hRc⟩ :=
    mme_log_joint_recipe_g_stage_compose (ell := 2) (lower := 1) (parts := 1) (P := S)
      (by norm_num) (fun _ ↦ lenAt n2 t * 2 ^ (1 - 1)) (onePart _) (fun _ ↦ S) (fun _ ↦ T)
      (fun i x h ↦ h 0) (fun _ ↦ Dst) (fun i x h _ ↦ gradeT i x h.1)
      (LogJointRecipeG.base (LogRecipe.boundary B))
      ((Fintype.card (Position (fun r ↦ t * n2 r)) + 1) ^
        (3 * Fintype.card (Cell (2 * 2 ^ (1 - 1)) 1104 parent2) *
          Fintype.card (CompleteSplit.CompleteWord 1))) 1
      (((585967670317 * 6 * 10 ^ 48 : ℕ) : ℝ) * t) 0
      (fun _ ↦ ⟨hDpos, hDtypes⟩) le_rfl le_rfl
      (by simp [hDrate]) (by simp [LogJointRecipeG.logOutputs, LogRecipe.logOutputs])
  -- the dimension product
  have hdims0 : R.a * R.b * R.c = B.a * B.b * B.c := by rw [hRa, hRb, hRc]; rfl
  have hdims1 : B.a * B.b * B.c =
      5 ^ (∑ j, Fintype.card {p : Fin (lenAt n2 t) // cellF p = j} * Boundary.ones (wd j)) := by
    rw [hB]
    exact concentrated_dims (fun j ↦ Fintype.card {p : Fin (lenAt n2 t) // cellF p = j}) wd
  have hsum : ∑ j, Fintype.card {p : Fin (lenAt n2 t) // cellF p = j} * Boundary.ones (wd j) =
      t * ∑ r : Fin 1104, 2 * D * (l2At r).2.1 * (D - (l2At r).2.2) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp ci, Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun r _ ↦ ?_)
    rw [← ones_sum r, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ ↦ ?_)
    have hc1 : Fintype.card {p : Fin (lenAt n2 t) // cellF p = ci ⟨r, e⟩} =
        t * m2 r e + t * m2 r (complement (htotal2 r) e) := by
      rw [← hcell ⟨r, e⟩]
      refine Fintype.card_congr ((positionsAt n2 t).subtypeEquiv ?_)
      intro q
      exact ci.injective.eq_iff
    have hc2 : Boundary.ones (wd (ci ⟨r, e⟩)) =
        if nextLetter (fun i ↦ (e.val i).val) = 1 then 1 else 0 := by
      rw [ones_const]
      show (if grd (ci ⟨r, e⟩) (zmode (grd (ci ⟨r, e⟩)) + 1) = 1 then 1 else 0) = _
      have hg : grd (ci ⟨r, e⟩) = fun i ↦ (e.val i).val := by
        funext i; show ((ci.symm (ci ⟨r, e⟩)).2.val i).val = _; rw [Equiv.symm_apply_apply]
      rw [hg]; beta_reduce; rw [nextLetter_eq (fun i ↦ (e.val i).val)]
    rw [hc1, hc2]; ring
  have hU : ((∑ r : Fin 1104, 2 * D * (l2At r).2.1 * (D - (l2At r).2.2) : ℕ) : ℝ) =
      13968264640400080378170674914282801769793717486676000000000000 := by
    rw [Uval_eq]; norm_num
  refine ⟨R, hR1, ?_, ?_, ?_, ?_⟩
  · refine le_trans hRX ?_
    rw [pow_one, mul_one, card_position]
    calc (t * A + 1) ^ Y ≤ ((t + 1) ^ A) ^ Y := Nat.pow_le_pow_left (bernoulli_nat t A) _
      _ = (t + 1) ^ (A * Y) := by rw [← pow_mul]
  · rw [hdims0, hdims1]; exact Nat.one_le_pow _ _ (by norm_num)
  · have h := hRrate; rw [add_zero] at h; exact h
  · rw [hdims0, hdims1, hsum, Nat.cast_pow, Real.log_pow, Nat.cast_mul t, hU]
    have h5 := log5_lower
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have key : ((37468424 * 6 * 10 ^ 53 : ℕ) : ℝ) ≤
        (13968264640400080378170674914282801769793717486676000000000000 : ℝ) * Real.log 5 := by
      have h1 : ((37468424 * 6 * 10 ^ 53 : ℕ) : ℝ) ≤
          (13968264640400080378170674914282801769793717486676000000000000 : ℝ) *
            (160943790 / 100000000) := by norm_num
      have h2 := mul_le_mul_of_nonneg_left h5
        (by norm_num : (0 : ℝ) ≤ 13968264640400080378170674914282801769793717486676000000000000)
      exact h1.trans h2
    have h3 := mul_le_mul_of_nonneg_left key ht0
    rw [Nat.cast_ofNat]
    calc ((37468424 * 6 * 10 ^ 53 : ℕ) : ℝ) * t = t * ((37468424 * 6 * 10 ^ 53 : ℕ) : ℝ) := by ring
      _ ≤ _ := h3
      _ = _ := by ring
