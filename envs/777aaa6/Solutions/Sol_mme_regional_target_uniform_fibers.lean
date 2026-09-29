-- Prove2me | solution 1 for mme_regional_target_uniform_fibers
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:07.851141+00:00
-- url     : https://prove2.me/submissions/b35365fe-c8a1-48fa-8ab0-52c84b3decf5

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Mathlib
open BigOperators MME.RecursiveThinSplit MME.RecursiveXHash MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

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

private theorem uniform_target_fibers {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, Split half (parent r) → ℕ)
    (i : Fin 3) (u v : Address half R parent n) (hu : u ∈ target (n := n) m) (hv : v ∈ target (n := n) m) :
    ((target (n := n) m).filter (fun w ↦ block i w = block i u)).card =
      ((target (n := n) m).filter (fun w ↦ block i w = block i v)).card := by
  classical
  have hu' : ∀ r, HasMarginalCounts (u r) (m r) := by
    exact (Finset.mem_filter.mp ((mme_recursive_x_hash_family_counts half R parent n m).1 hu)).2
  have hv' : ∀ r, HasMarginalCounts (v r) (m r) := by
    exact (Finset.mem_filter.mp ((mme_recursive_x_hash_family_counts half R parent n m).1 hv)).2
  have hm (r : Fin R) := matching_perm (block i u r) (block i v r)
    (fun a ↦ (hu' r i a).trans (hv' r i a).symm)
  choose σ hσ using hm
  let E : Address half R parent n ≃ Address half R parent n :=
    { toFun := fun w r t ↦ w r (σ r t)
      invFun := fun w r t ↦ w r ((σ r).symm t)
      left_inv := by intro w; funext r t; simp
      right_inv := by intro w; funext r t; simp }
  have hamb (w : Address half R parent n) : E w ∈ target (n := n) m ↔ w ∈ target (n := n) m := by
    simp only [target, Finset.mem_filter, Finset.mem_univ, true_and, HasJointCounts]
    simpa only [E] using forall_congr' (fun r ↦ forall_congr' (fun c ↦
      ((count_perm (w r) (σ r) c).congr_left)))
  have hb (w : Address half R parent n) :
      block i (E w) = block i v ↔ block i w = block i u := by
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

theorem solution {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3)
    (a : Address half R parent n) (ha : a ∈ target m) :
    (∀ b ∈ target m,
      ((target (n := n) m).filter (fun w ↦ block i w = block i b)).card =
        ((target (n := n) m).filter (fun w ↦ block i w = block i a)).card) ∧
    ((target (n := n) m).card = ((target (n := n) m).image (block i)).card *
      ((target (n := n) m).filter (fun w ↦ block i w = block i a)).card) := by
  classical
  refine ⟨fun b hb ↦ uniform_target_fibers m i b a hb ha,?_⟩
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (target (n := n) m) ((target (n := n) m).image (block i)) (block i)
  have hall : (target (n := n) m).filter
      (fun w ↦ block i w ∈ (target (n := n) m).image (block i)) = target (n := n) m := by
    ext w
    simp only [Finset.mem_filter,and_iff_left_iff_imp]
    exact fun hw ↦ Finset.mem_image_of_mem _ hw
  rw [hall] at h
  rw [← h]
  have heq : ∀ x ∈ (target (n := n) m).image (block i),
      ((target (n := n) m).filter (fun w ↦ block i w = x)).card =
        ((target (n := n) m).filter (fun w ↦ block i w = block i a)).card := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact uniform_target_fibers m i b a hb ha
  simp_rw [Finset.sum_congr rfl heq,Finset.sum_const,nsmul_eq_mul]
  simp
