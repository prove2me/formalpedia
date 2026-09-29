-- Prove2me | solution 1 for mme_recursive_x_hash_family_counts
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-11T22:45:38.527202+00:00
-- url     : https://prove2.me/submissions/cf11794b-4c8d-4c27-b44d-a8a0dbe6f712

import Definitions.Def_mme_recursive_x_hash_families
import Theorems.Thm_mme_recursive_thin_split_marginal_joint_counts

open BigOperators MME.RecursiveThinSplit MME.RecursiveXHash

set_option autoImplicit false

private theorem count_map {A I : Type*} [Fintype A] [DecidableEq A] [DecidableEq I]
    {n : ℕ} (w : Fin n → A) (coord : A → I) (j : I) :
    count (fun t ↦ coord (w t)) j =
      ∑ a : {a // coord a = j}, count w a.val := by
  classical
  let s := Finset.univ.filter (fun a : A ↦ coord a = j)
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) s w
  have hsub := Finset.sum_subtype (F := inferInstance) s
    (fun a ↦ show a ∈ s ↔ coord a = j by simp [s]) (count w)
  rw [← hsub]
  simpa [count, s] using h.symm

private theorem count_perm {A : Type*} [DecidableEq A] {n : ℕ}
    (w : Fin n → A) (σ : Equiv.Perm (Fin n)) (a : A) :
    count (fun t ↦ w (σ t)) a = count w a := by
  apply Finset.card_equiv σ
  intro t
  simp

private theorem matching_perm {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (u v : Fin n → A) (h : ∀ a, count u a = count v a) :
    ∃ σ : Equiv.Perm (Fin n), ∀ t, u (σ t) = v t := by
  classical
  have hc (a : A) : Fintype.card {t // v t = a} = Fintype.card {t // u t = a} := by
    simpa [Fintype.card_subtype, count] using (h a).symm
  let es := fun a ↦ Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv es, Equiv.ofFiberEquiv_map es⟩

private theorem uniform_fibers {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, Split half (parent r) → ℕ)
    (u v : Address half R parent n) (hu : u ∈ ambient (n := n) m) (hv : v ∈ ambient (n := n) m) :
    ((ambient (n := n) m).filter (fun w ↦ block 0 w = block 0 u)).card =
      ((ambient (n := n) m).filter (fun w ↦ block 0 w = block 0 v)).card := by
  classical
  have hu' : ∀ r, HasMarginalCounts (u r) (m r) := by simpa [ambient] using hu
  have hv' : ∀ r, HasMarginalCounts (v r) (m r) := by simpa [ambient] using hv
  have hm (r : Fin R) := matching_perm (block 0 u r) (block 0 v r)
    (fun a ↦ (hu' r 0 a).trans (hv' r 0 a).symm)
  choose σ hσ using hm
  let E : Address half R parent n ≃ Address half R parent n :=
    { toFun := fun w r t ↦ w r (σ r t)
      invFun := fun w r t ↦ w r ((σ r).symm t)
      left_inv := by intro w; funext r t; simp
      right_inv := by intro w; funext r t; simp }
  have hamb (w : Address half R parent n) : E w ∈ ambient (n := n) m ↔ w ∈ ambient (n := n) m := by
    simp only [ambient, Finset.mem_filter, Finset.mem_univ, true_and, HasMarginalCounts]
    have hc (r : Fin R) (i : Fin 3) (j : Fin (half + 1)) :=
      count_perm (fun t ↦ (w r t).val i) (σ r) j
    simpa only [E] using forall_congr' (fun r ↦ forall_congr' (fun i ↦
      forall_congr' (fun j ↦ (hc r i j).congr_left)))
  have hb (w : Address half R parent n) :
      block 0 (E w) = block 0 v ↔ block 0 w = block 0 u := by
    constructor
    · intro h
      funext r t
      have hh := congrFun (congrFun h r) ((σ r).symm t)
      have hs := hσ r ((σ r).symm t)
      simpa [E, block] using hh.trans hs.symm
    · intro h
      funext r t
      exact (congrFun (congrFun h r) (σ r t)).trans (hσ r t)
  apply Finset.card_equiv E
  intro w
  simp only [Finset.mem_filter, hamb, hb]

theorem solution (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ) :
    target (n := n) m ⊆ ambient (n := n) m ∧
    (∀ a ∈ ambient (n := n) m,
      (ambient (n := n) m).card = ((ambient (n := n) m).image (block 0)).card *
        ((ambient (n := n) m).filter (fun b ↦ block 0 b = block 0 a)).card) ∧
    ((∀ r, ∃ i, parent r i ≤ 1) → ambient (n := n) m = target m) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    simp only [target, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [ambient, Finset.mem_filter, Finset.mem_univ, true_and]
    intro r i j
    rw [count_map (w r) (fun a ↦ a.val i) j]
    exact Finset.sum_congr rfl (fun a _ ↦ hw r a.val)
  · intro a ha
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (ambient (n := n) m) ((ambient (n := n) m).image (block 0)) (block 0)
    have hall : (ambient (n := n) m).filter
        (fun w ↦ block 0 w ∈ (ambient (n := n) m).image (block 0)) = ambient (n := n) m := by
      ext w
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      exact fun hw ↦ Finset.mem_image_of_mem _ hw
    rw [hall] at h
    rw [← h]
    have heq : ∀ x ∈ (ambient (n := n) m).image (block 0),
        ((ambient (n := n) m).filter (fun w ↦ block 0 w = x)).card =
          ((ambient (n := n) m).filter (fun w ↦ block 0 w = block 0 a)).card := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      exact uniform_fibers m b a hb ha
    simp_rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    simp
  · intro hthin
    ext w
    simp only [ambient, target, Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_congr' (fun r ↦
      (mme_recursive_thin_split_marginal_joint_counts half (parent r) (hthin r)
        (n r) (m r)).1 (w r))
