-- Prove2me | solution 1 for BookSixth.bregman_minc_geometric_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T16:45:21.764882+00:00
-- url     : https://prove2.me/submissions/154d83db-f2ab-428e-a29b-c6d34180b99e

import Mathlib
import Definitions.Def_BregmanMincWeights

open scoped BigOperators
open BregmanMincWeights

/- Direct candidate for the geometric-mean child. Lean execution and proof
   validation remain remote-only. -/
namespace BookClaimB

theorem prod_suffix_card {α : Type*} [LinearOrder α] (s : Finset α) :
    (∏ x ∈ s, (s.filter (fun y => x ≤ y)).card) = s.card.factorial := by
  classical
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a s ha ih =>
    have hnot : a ∉ s := by
      intro h
      exact (lt_irrefl a) (ha a h)
    have hfirst : (insert a s).filter (fun y => a ≤ y) = insert a s := by
      apply Finset.filter_true_of_mem
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact le_rfl
      · exact le_of_lt (ha y hy)
    have hrest : ∀ x ∈ s,
        (insert a s).filter (fun y => x ≤ y) = s.filter (fun y => x ≤ y) := by
      intro x hx
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hy, hxy⟩
        · exact False.elim ((not_le_of_gt (ha x hx)) hxy)
        · exact ⟨hy, hxy⟩
      · rintro ⟨hy, hxy⟩
        exact ⟨Or.inr hy, hxy⟩
    rw [Finset.prod_insert hnot, hfirst]
    simp_rw [Finset.card_insert_of_notMem hnot]
    rw [Finset.prod_congr rfl (fun x hx => congrArg Finset.card (hrest x hx)), ih]
    exact (Nat.factorial_succ s.card).symm

theorem avail_relabel {n : ℕ} (S : Finset (Fin n))
    (e π : Equiv.Perm (Fin n)) (i : Fin n)
    (hS : ∀ t, t ∈ S ↔ e t ∈ S) :
    avail (e i) S (π.trans e) = avail i S π := by
  classical
  symm
  unfold avail
  apply Finset.card_equiv e
  intro t
  simp only [Finset.mem_filter]
  change (t ∈ S ∧ π.symm i ≤ π.symm t) ↔
    (e t ∈ S ∧ π.symm (e.symm (e i)) ≤ π.symm (e.symm (e t)))
  simp only [Equiv.symm_apply_apply, hS t]

theorem prod_avail_relabel {n : ℕ} (S : Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (i : Fin n)
    (hS : ∀ t, t ∈ S ↔ e t ∈ S) :
    (∏ π : Equiv.Perm (Fin n), avail i S π) =
      ∏ π : Equiv.Perm (Fin n), avail (e i) S π := by
  classical
  let E : Equiv.Perm (Equiv.Perm (Fin n)) :=
    { toFun := fun π => π.trans e
      invFun := fun π => π.trans e.symm
      left_inv := by
        intro π
        apply Equiv.ext
        intro x
        exact e.symm_apply_apply (π x)
      right_inv := by
        intro π
        apply Equiv.ext
        intro x
        exact e.apply_symm_apply (π x) }
  apply Fintype.prod_equiv E
    (fun π => avail i S π) (fun π => avail (e i) S π)
  intro π
  exact (avail_relabel S e π i hS).symm

theorem prod_avail_eq_of_mem {n : ℕ} (S : Finset (Fin n))
    (i j : Fin n) (hi : i ∈ S) (hj : j ∈ S) :
    (∏ π : Equiv.Perm (Fin n), avail i S π) =
      ∏ π : Equiv.Perm (Fin n), avail j S π := by
  classical
  have hS : ∀ t, t ∈ S ↔ Equiv.swap i j t ∈ S := by
    intro t
    by_cases hti : t = i
    · subst t
      simp [hi, hj]
    by_cases htj : t = j
    · subst t
      simp [hi, hj]
    simp only [Equiv.swap_apply_of_ne_of_ne hti htj]
  simpa only [Equiv.swap_apply_left] using
    prod_avail_relabel S (Equiv.swap i j) i hS

theorem prod_avail_fixed_order {n : ℕ} (S : Finset (Fin n))
    (π : Equiv.Perm (Fin n)) :
    (∏ i ∈ S, avail i S π) = S.card.factorial := by
  classical
  let T := S.image π.symm
  have hmem : ∀ i, i ∈ S ↔ π.symm i ∈ T := by
    intro i
    simp [T]
  have hcount : ∀ i, avail i S π =
      (T.filter (fun y => π.symm i ≤ y)).card := by
    intro i
    unfold avail
    apply Finset.card_equiv π.symm
    intro t
    simp only [Finset.mem_filter, ← hmem t]
  have hprod : (∏ i ∈ S, avail i S π) =
      ∏ x ∈ T, (T.filter (fun y => x ≤ y)).card :=
    Finset.prod_equiv π.symm hmem (fun i _ => hcount i)
  rw [hprod, prod_suffix_card]
  congr 1
  exact (Finset.card_equiv π.symm hmem).symm

theorem prod_avail_pow_card {n : ℕ} (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) :
    (∏ π : Equiv.Perm (Fin n), avail i S π) ^ S.card =
      S.card.factorial ^ n.factorial := by
  classical
  calc
    (∏ π : Equiv.Perm (Fin n), avail i S π) ^ S.card =
        ∏ j ∈ S, ∏ π : Equiv.Perm (Fin n), avail i S π := by
      rw [Finset.prod_const]
    _ = ∏ j ∈ S, ∏ π : Equiv.Perm (Fin n), avail j S π := by
      apply Finset.prod_congr rfl
      intro j hj
      exact prod_avail_eq_of_mem S i j hi hj
    _ = ∏ π : Equiv.Perm (Fin n), ∏ j ∈ S, avail j S π :=
      Finset.prod_comm
    _ = ∏ _π : Equiv.Perm (Fin n), S.card.factorial := by
      apply Finset.prod_congr rfl
      intro π _
      exact prod_avail_fixed_order S π
    _ = S.card.factorial ^ n.factorial := by
      simp [Fintype.card_perm]

theorem avail_pos {n : ℕ} (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) (π : Equiv.Perm (Fin n)) :
    0 < avail i S π := by
  classical
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, le_rfl⟩⟩

theorem sum_log_avail {n : ℕ} (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) :
    (∑ π : Equiv.Perm (Fin n), Real.log (avail i S π : ℝ)) =
      (n.factorial : ℝ) / (S.card : ℝ) * Real.log (S.card.factorial : ℝ) := by
  classical
  have hp : (∏ π : Equiv.Perm (Fin n), (avail i S π : ℝ)) ^ S.card =
      (S.card.factorial : ℝ) ^ n.factorial := by
    exact_mod_cast prod_avail_pow_card S i hi
  have hlog := congrArg Real.log hp
  rw [Real.log_pow, Real.log_pow,
    Real.log_prod (fun π _ => ne_of_gt (by exact_mod_cast avail_pos S i hi π))] at hlog
  have hd : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨i, hi⟩))
  calc
    (∑ π : Equiv.Perm (Fin n), Real.log (avail i S π : ℝ)) =
        (n.factorial : ℝ) * Real.log (S.card.factorial : ℝ) / (S.card : ℝ) := by
      apply (eq_div_iff hd).mpr
      nlinarith [hlog]
    _ = _ := by ring

theorem card_preS {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hA : ∀ i j, A i j ≤ 1) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (preS A σ i).card = ∑ j, A i j := by
  classical
  unfold preS
  rw [Finset.card_filter]
  calc
    (∑ j : Fin n, if A i (σ j) = 1 then 1 else 0) = ∑ j : Fin n, A i (σ j) := by
      apply Finset.sum_congr rfl
      intro j _
      have hle := hA i (σ j)
      by_cases h : A i (σ j) = 1
      · simp [h]
      · simp only [if_neg h]
        omega
    _ = ∑ j, A i j := Equiv.sum_comp σ (fun j => A i j)

end BookClaimB

theorem solution (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ)
    (hA : ∀ i j, A i j ≤ 1) (hrows : ∀ i, 0 < ∑ j, A i j)
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ aSys A) :
    (∏ π : Equiv.Perm (Fin n), qW A σ π) ^ ((n.factorial : ℝ)⁻¹) =
      ∏ i : Fin n, ((Nat.factorial (∑ j, A i j) : ℕ) : ℝ) ^
        (-(1 : ℝ) / ((∑ j, A i j : ℕ) : ℝ)) := by
  classical
  have hcompat : ∀ i, A i (σ i) = 1 := (Finset.mem_filter.mp hσ).2
  have hmem : ∀ i, i ∈ preS A σ i := by
    intro i
    simp [preS, hcompat i]
  have havail : ∀ i π, (0 : ℝ) < (avail i (preS A σ i) π : ℝ) := by
    intro i π
    exact_mod_cast BookClaimB.avail_pos (preS A σ i) i (hmem i) π
  have hq : ∀ π, 0 < qW A σ π := by
    intro π
    unfold qW
    exact Finset.prod_pos (fun i _ => div_pos zero_lt_one (havail i π))
  have hprod : 0 < ∏ π : Equiv.Perm (Fin n), qW A σ π :=
    Finset.prod_pos (fun π _ => hq π)
  have hfac : ∀ i : Fin n, (0 : ℝ) < ((∑ j, A i j).factorial : ℝ) := by
    intro i
    exact_mod_cast Nat.factorial_pos (∑ j, A i j)
  have hN : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.factorial_pos n))
  have hlogq : ∀ π, Real.log (qW A σ π) =
      ∑ i : Fin n, -Real.log (avail i (preS A σ i) π : ℝ) := by
    intro π
    unfold qW
    rw [Real.log_prod (fun i _ => ne_of_gt (div_pos zero_lt_one (havail i π)))]
    simp only [one_div, Real.log_inv]
  apply Real.log_injOn_pos
    (Real.rpow_pos_of_pos hprod _)
    (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hfac i) _))
  rw [Real.log_rpow hprod,
    Real.log_prod (fun π _ => ne_of_gt (hq π)),
    Real.log_prod (fun i _ => ne_of_gt (Real.rpow_pos_of_pos (hfac i) _))]
  simp_rw [hlogq]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_neg_distrib,
    BookClaimB.sum_log_avail (preS A σ i) i (hmem i),
    BookClaimB.card_preS A hA σ i, Real.log_rpow (hfac i)]
  have hd : ((∑ j, A i j : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hrows i))
  field_simp [hN, hd] <;> ring
