-- Prove2me | solution 1 for Heisenberg125.smallDavenport_multiplicative_zmod_sq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-21T08:26:00.409009+00:00
-- url     : https://prove2.me/submissions/252859a8-b195-4727-88d0-8604a669a713

import Theorems.Thm_Heisenberg125_exists_nonempty_zeroSum_sublist
import Theorems.Thm_Heisenberg125_isProductOne_iff_sum_eq_zero
import Theorems.Thm_Heisenberg125_Heis_eq_zero_of_cast_eq_zero
import Theorems.Thm_Heisenberg125_ProductOneFree_length_le_smallDavenport

open Heisenberg125 Multiplicative

variable {p : ℕ}

private lemma fst_list_sum {B C : Type*} [AddCommMonoid B] [AddCommMonoid C]
    (L : List (B × C)) : L.sum.1 = (L.map Prod.fst).sum := by
  induction L with
  | nil => rfl
  | cons g L ih => simp [ih]

private lemma snd_list_sum {B C : Type*} [AddCommMonoid B] [AddCommMonoid C]
    (L : List (B × C)) : L.sum.2 = (L.map Prod.snd).sum := by
  induction L with
  | nil => rfl
  | cons g L ih => simp [ih]

private lemma productOneFree_nil {G : Type*} [Group G] :
    ProductOneFree ([] : List G) := by
  rintro T hT hne
  exact absurd (List.eq_nil_of_sublist_nil hT) hne

private theorem productOneFree_basis_seq (hp : 0 < p) :
    ProductOneFree
      (List.replicate (p - 1) (ofAdd ((1 : ZMod p), (0 : ZMod p))) ++
        List.replicate (p - 1) (ofAdd ((0 : ZMod p), (1 : ZMod p)))) := by
  intro T hT hne hone
  obtain ⟨T1, T2, rfl, h1, h2⟩ := List.sublist_append_iff.1 hT
  obtain ⟨i, hi, rfl⟩ := List.sublist_replicate_iff.1 h1
  obtain ⟨j, hj, rfl⟩ := List.sublist_replicate_iff.1 h2
  rw [isProductOne_iff_sum_eq_zero] at hone
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, toAdd_ofAdd] at hone
  have hfst : (i : ZMod p) = 0 := by
    have h := congrArg Prod.fst hone
    simpa [Prod.smul_mk, nsmul_eq_mul] using h
  have hsnd : (j : ZMod p) = 0 := by
    have h := congrArg Prod.snd hone
    simpa [Prod.smul_mk, nsmul_eq_mul] using h
  have hi0 := Heisenberg125.Heis.eq_zero_of_cast_eq_zero hp hi hfst
  have hj0 := Heisenberg125.Heis.eq_zero_of_cast_eq_zero hp hj hsnd
  subst hi0
  subst hj0
  exact hne (by simp)

theorem solution [Fact p.Prime] :
    smallDavenport (Multiplicative (ZMod p × ZMod p)) = 2 * p - 2 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨0, ⟨[], rfl, productOneFree_nil⟩⟩ ?_
    rintro n ⟨L, rfl, hL⟩
    by_contra hlen
    push_neg at hlen
    obtain ⟨T, hTsub, hTne, h1, h2⟩ :=
      exists_nonempty_zeroSum_sublist L (fun g => (toAdd g).1)
        (fun g => (toAdd g).2) (by omega)
    refine hL T hTsub hTne ?_
    rw [isProductOne_iff_sum_eq_zero]
    refine Prod.ext ?_ ?_
    · rw [fst_list_sum, List.map_map]
      simpa using h1
    · rw [snd_list_sum, List.map_map]
      simpa using h2
  · have h := (productOneFree_basis_seq (p := p) hp).length_le_smallDavenport
    simp only [List.length_append, List.length_replicate] at h
    omega
