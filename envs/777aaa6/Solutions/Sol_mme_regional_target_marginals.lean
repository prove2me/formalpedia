-- Prove2me | solution 1 for mme_regional_target_marginals
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:09.884701+00:00
-- url     : https://prove2.me/submissions/fce6cfad-e224-43c8-84de-c27e4b780c6a

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Mathlib
open BigOperators MME.RecursiveThinSplit MME.RecursiveXHash MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

private theorem count_perm {A : Type*} [DecidableEq A] {n : ℕ}
    (w : Fin n → A) (s : Equiv.Perm (Fin n)) (a : A) : count (fun t ↦ w (s t)) a = count w a := by
  apply Finset.card_equiv s
  intro t
  simp

private theorem count_sum {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ} (w : Fin n → A) :
    ∑ a, count w a = n := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv w)
  simpa only [Fintype.card_sigma,Fintype.card_subtype,Fintype.card_fin,count] using h

private theorem matching_perm {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (u v : Fin n → A) (h : ∀ a, count u a = count v a) :
    ∃ s : Equiv.Perm (Fin n), ∀ t, u (s t) = v t := by
  classical
  have hc (a : A) : Fintype.card {t // v t = a} = Fintype.card {t // u t = a} := by
    simpa [Fintype.card_subtype,count] using (h a).symm
  let es := fun a ↦ Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv es,Equiv.ofFiberEquiv_map es⟩

theorem solution {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3)
    (a : Address half R parent n) (ha : a ∈ target m) :
    (∀ r, ∑ c, m r c = n r) ∧
    (∀ r, ∑ j, marginalCounts m i r j = n r) ∧
    ((target (n := n) m).image (block i) =
      Finset.univ.filter (fun y : ∀ r, Fin (n r) → Fin (half + 1) ↦
        ∀ r j, count (y r) j = marginalCounts m i r j)) := by
  classical
  have hjoint : ∀ r c, count (a r) c = m r c := (Finset.mem_filter.mp ha).2
  have hmargin : ∀ r j, count (block i a r) j = marginalCounts m i r j :=
    fun r j ↦ (Finset.mem_filter.mp ((mme_recursive_x_hash_family_counts half R parent n m).1 ha)).2 r i j
  refine ⟨fun r ↦ ?_,fun r ↦ ?_,?_⟩
  · simpa only [hjoint] using count_sum (a r)
  · simpa only [hmargin] using count_sum (block i a r)
  · ext y
    constructor
    · rintro hy
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun r j ↦
        (Finset.mem_filter.mp ((mme_recursive_x_hash_family_counts half R parent n m).1 hb)).2 r i j⟩
    · intro hy
      have hy' := (Finset.mem_filter.mp hy).2
      have hm r := matching_perm (block i a r) (y r) (fun j ↦ (hmargin r j).trans (hy' r j).symm)
      choose s hs using hm
      let b : Address half R parent n := fun r t ↦ a r (s r t)
      have hb : b ∈ target m := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,fun r c ↦ ?_⟩
        exact (count_perm (a r) (s r) c).trans (hjoint r c)
      exact Finset.mem_image.mpr ⟨b,hb,funext fun r ↦ funext (hs r)⟩
