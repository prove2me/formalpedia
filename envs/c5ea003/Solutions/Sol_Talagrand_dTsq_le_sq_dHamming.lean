-- Prove2me | solution 1 for Talagrand.dTsq_le_sq_dHamming
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:43:37.854591+00:00
-- url     : https://prove2.me/submissions/d8af65e1-d6a0-40e0-b322-b5608717603b

import Mathlib
import Definitions.Def_Probability_TalagrandDefs
import Definitions.Def_Probability_TalagrandDuality

open Finset Talagrand in
theorem solution {α : Type*} [DecidableEq α] {n : ℕ} {A : Finset (Fin n → α)}
    (hA : A.Nonempty) (x : Fin n → α) :
    ∃ w : Fin n → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, (w i) ^ 2 ≤ 1) ∧
      dTsq A x ≤ (dHamming w A x) ^ 2 := by
  classical
  have hH0 : ∀ u v : α, 0 ≤ hamm u v := fun u v => by
    unfold hamm
    split_ifs <;> norm_num
  -- Hamming vectors of the points of `A`, indexed by the subtype
  let H : {y // y ∈ A} → Fin n → ℝ := fun y i => hamm (x i) (y.1 i)
  let V : ({y // y ∈ A} → ℝ) → Fin n → ℝ := fun l i => ∑ y, l y * H y i
  let F : ({y // y ∈ A} → ℝ) → ℝ := fun l => ∑ i, (V l i) ^ 2
  have hFc : Continuous F :=
    continuous_finsetSum _ (fun i _ =>
      (continuous_finsetSum _ (fun y _ => (continuous_apply y).mul continuous_const)).pow 2)
  obtain ⟨y0, hy0⟩ := hA
  have hne : (stdSimplex ℝ {y // y ∈ A}).Nonempty :=
    ⟨Pi.single ⟨y0, hy0⟩ 1, single_mem_stdSimplex ℝ _⟩
  obtain ⟨l, hl, hmin⟩ := (isCompact_stdSimplex ℝ {y // y ∈ A}).exists_isMinOn hne hFc.continuousOn
  set v : Fin n → ℝ := V l with hv
  -- the minimiser is representable
  have hrep : IsRep A x v := by
    refine ⟨Fintype.card {y // y ∈ A}, fun j => l ((Fintype.equivFin _).symm j),
      fun j => ((Fintype.equivFin _).symm j).1, fun j => hl.1 _, ?_,
      fun j => ((Fintype.equivFin _).symm j).2, fun i => ?_⟩
    · rw [Equiv.sum_comp (Fintype.equivFin {y // y ∈ A}).symm (fun y => l y)]
      exact hl.2
    · exact (Equiv.sum_comp (Fintype.equivFin {y // y ∈ A}).symm
        (fun y => l y * hamm (x i) (y.1 i))).symm
  have hvnn : ∀ i, 0 ≤ v i := fun i =>
    Finset.sum_nonneg (fun y _ => mul_nonneg (hl.1 y) (hH0 _ _))
  -- the variational inequality at the minimiser
  have hvar : ∀ y : {y // y ∈ A}, ∑ i, v i ^ 2 ≤ ∑ i, v i * H y i := by
    intro y
    set D := ∑ i, (H y i - v i) ^ 2 with hD
    set c := ∑ i, v i * (H y i - v i) with hc
    have hD0 : 0 ≤ D := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    set e1 : {y // y ∈ A} → ℝ := Pi.single y 1 with he1
    have he1y : ∀ z, e1 z = if z = y then 1 else 0 := by
      intro z
      simp only [he1, Pi.single_apply]
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ 2 * c + t * D := by
      intro t ht0 ht1
      have hmem : (1 - t) • l + t • e1 ∈ stdSimplex ℝ {y // y ∈ A} :=
        convex_stdSimplex ℝ _ hl (single_mem_stdSimplex ℝ y : e1 ∈ _) (by linarith) ht0.le (by ring)
      have h1 := (isMinOn_iff.1 hmin) _ hmem
      have hVt : ∀ i, V ((1 - t) • l + t • e1) i = v i + t * (H y i - v i) := by
        intro i
        show ∑ z, ((1 - t) • l + t • e1) z * H z i = _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
          mul_assoc, ← Finset.mul_sum, he1y, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hv]
        ring
      have hexp : F ((1 - t) • l + t • e1) = ∑ i, v i ^ 2 + 2 * t * c + t ^ 2 * D := by
        show ∑ i, (V ((1 - t) • l + t • e1) i) ^ 2 = _
        simp only [hVt, hc, hD, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have hFl : F l = ∑ i, v i ^ 2 := rfl
      rw [hexp, hFl] at h1
      have h2 : 0 ≤ t * (2 * c + t * D) := by nlinarith
      exact (mul_nonneg_iff_of_pos_left ht0).1 h2
    by_contra hneg
    have hc0 : c < 0 := by
      have : ∑ i, v i * H y i - ∑ i, v i ^ 2 = c := by
        rw [hc, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      linarith [not_le.1 hneg]
    set t := min 1 (-c / (D + 1)) with ht
    have htpos : 0 < t := lt_min one_pos (div_pos (by linarith) (by linarith))
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ -c / (D + 1) := min_le_right _ _
    have h3 := key t htpos ht1
    have h4 : t * D ≤ -c := by
      have h5 : t * (D + 1) ≤ -c := by
        rw [le_div_iff₀ (by linarith)] at ht2
        exact ht2
      nlinarith
    linarith
  set s := ∑ i, v i ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hdT : dTsq A x ≤ s := by
    unfold dTsq
    exact csInf_le ⟨0, by
      rintro _ ⟨v', -, rfl⟩
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)⟩ ⟨v, hrep, rfl⟩
  rcases eq_or_lt_of_le hs0 with hs00 | hspos
  · refine ⟨0, fun _ => le_rfl, by simp, ?_⟩
    have hd : dHamming 0 A x = 0 := by
      unfold dHamming
      have hset : {t : ℝ | ∃ y ∈ A, t = ∑ i, (0 : Fin n → ℝ) i * hamm (x i) (y i)} = {0} := by
        ext t
        simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Set.mem_setOf_eq,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨y, -, rfl⟩
          rfl
        · rintro rfl
          exact ⟨y0, hy0, rfl⟩
      rw [hset, csInf_singleton]
    rw [hd]
    linarith
  · set r := Real.sqrt s with hr
    have hrpos : 0 < r := Real.sqrt_pos.2 hspos
    have hrr : r * r = s := Real.mul_self_sqrt hs0
    refine ⟨fun i => v i / r, fun i => div_nonneg (hvnn i) hrpos.le, ?_, ?_⟩
    · have e : ∑ i, (v i / r) ^ 2 = s / (r * r) := by
        rw [hs, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [div_pow, sq r]
      rw [e, hrr, div_self hspos.ne']
    · have hge : r ≤ dHamming (fun i => v i / r) A x := by
        unfold dHamming
        refine le_csInf ⟨∑ i, v i / r * hamm (x i) (y0 i), y0, hy0, rfl⟩ ?_
        rintro _ ⟨y, hy, rfl⟩
        have h1 := hvar ⟨y, hy⟩
        have e : ∑ i, v i / r * hamm (x i) (y i) = (∑ i, v i * hamm (x i) (y i)) / r := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [e, le_div_iff₀ hrpos]
        have h2 : ∑ i, v i * H ⟨y, hy⟩ i = ∑ i, v i * hamm (x i) (y i) := rfl
        linarith
      nlinarith [mul_le_mul hge hge hrpos.le (le_trans hrpos.le hge)]
