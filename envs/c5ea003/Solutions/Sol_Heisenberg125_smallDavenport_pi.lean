-- Prove2me | solution 1 for Heisenberg125.smallDavenport_pi
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T05:45:12.59989+00:00
-- url     : https://prove2.me/submissions/a0a6b57e-90c4-4d63-b231-e1f1ce4d001a

import Theorems.Thm_Heisenberg125_exists_nonempty_zeroSum_sublist_family
import Theorems.Thm_Heisenberg125_productOneFree_piBasisSeq
import Theorems.Thm_Heisenberg125_ProductOneFree_length_le_smallDavenport
import Theorems.Thm_Heisenberg125_isProductOne_iff_sum_eq_zero

open Heisenberg125 Multiplicative

private lemma productOneFree_nil {G : Type*} [Group G] :
    ProductOneFree ([] : List G) := by
  rintro T hT hne
  exact absurd (List.eq_nil_of_sublist_nil hT) hne

private lemma list_sum_apply {ι A : Type*} [AddCommMonoid A]
    (L : List (ι → A)) (j : ι) :
    L.sum j = (L.map (fun f => f j)).sum := by
  induction L with
  | nil => rfl
  | cons f L ih => simp [ih]

private lemma mapped_sum_eq_zero {p k : ℕ}
    (T : List (Multiplicative (Fin k → ZMod p)))
    (hT : ∀ j, (T.map (fun g => (toAdd g) j)).sum = 0) :
    (T.map toAdd).sum = 0 := by
  funext j
  rw [list_sum_apply, List.map_map]
  simpa using hT j

theorem solution (p k : ℕ) [Fact p.Prime] :
    smallDavenport (Multiplicative (Fin k → ZMod p)) = k * (p - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  apply le_antisymm
  · refine csSup_le ⟨0, ⟨[], rfl, productOneFree_nil⟩⟩ ?_
    rintro n ⟨L, rfl, hL⟩
    by_contra hlen
    push_neg at hlen
    obtain ⟨T, hTsub, hTne, hTsum⟩ :=
      exists_nonempty_zeroSum_sublist_family L
        (fun j g => (toAdd g) j) hlen
    refine hL T hTsub hTne ?_
    rw [isProductOne_iff_sum_eq_zero]
    exact mapped_sum_eq_zero T hTsum
  · have h :=
      (productOneFree_piBasisSeq (p := p) (k := k) hp).length_le_smallDavenport
    simpa [piBasisSeq] using h
