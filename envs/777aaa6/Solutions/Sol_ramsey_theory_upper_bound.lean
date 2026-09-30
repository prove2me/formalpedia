-- Prove2me | solution 1 for ramsey_theory_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:02:29.112838+00:00
-- url     : https://prove2.me/submissions/854d8569-780b-4e44-aa84-94055b027fd3

import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum

private def Homogeneous {α : Type*} (col : Sym2 α → Bool) (S : Finset α) (c : Bool) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = c

private theorem homogeneous_insert {α : Type*} [DecidableEq α]
    (col : Sym2 α → Bool) (S : Finset α) (v : α) (c : Bool)
    (hS : Homogeneous col S c) (hv : ∀ x ∈ S, col (Sym2.mk v x) = c) :
    Homogeneous col (insert v S) c := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with hav | haS
  · rcases Finset.mem_insert.mp hb with hbv | hbS
    · exact (hab (hav.trans hbv.symm)).elim
    · rw [hav]
      exact hv b hbS
  · rcases Finset.mem_insert.mp hb with hbv | hbS
    · rw [hbv, Sym2.eq_swap]
      exact hv a haS
    · exact hS a haS b hbS hab

private theorem ramsey_card {α : Type*} [DecidableEq α] (col : Sym2 α → Bool)
    (r s : ℕ) (S : Finset α) (hcard : 2 ^ (r + s) ≤ S.card) :
    (∃ T ⊆ S, T.card = r ∧ Homogeneous col T true) ∨
      (∃ T ⊆ S, T.card = s ∧ Homogeneous col T false) := by
  classical
  induction r generalizing s S with
  | zero =>
      left
      exact ⟨∅, Finset.empty_subset _, rfl, by simp [Homogeneous]⟩
  | succ r hir =>
      induction s generalizing S with
      | zero =>
          right
          exact ⟨∅, Finset.empty_subset _, rfl, by simp [Homogeneous]⟩
      | succ s his =>
          have hpos : 0 < S.card := lt_of_lt_of_le (pow_pos (by decide) _) hcard
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
          let R := (S.erase v).filter fun x => col (Sym2.mk v x) = true
          let B := (S.erase v).filter fun x => ¬ col (Sym2.mk v x) = true
          have hpartition : R.card + B.card = (S.erase v).card :=
            Finset.card_filter_add_card_filter_not (s := S.erase v) _
          have herase := Finset.card_erase_add_one hv
          have hdouble : 2 * 2 ^ (r + s + 1) ≤ S.card := by
            have he : r + 1 + (s + 1) = (r + s + 1) + 1 := by omega
            simpa only [Nat.succ_eq_add_one, he, pow_succ, Nat.mul_comm] using hcard
          have hRsub : R ⊆ S := fun x hx =>
            (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
          have hBsub : B ⊆ S := fun x hx =>
            (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
          by_cases hR : 2 ^ (r + s + 1) ≤ R.card
          · rcases hir (s + 1) R (by simpa only [Nat.add_assoc] using hR) with h | h
            · obtain ⟨T, hT, hTcard, hmono⟩ := h
              have hvT : v ∉ T := by
                intro hmem
                exact (Finset.mem_erase.mp (Finset.mem_filter.mp (hT hmem)).1).1 rfl
              left
              refine ⟨insert v T, Finset.insert_subset hv (hT.trans hRsub), ?_, ?_⟩
              · simpa only [Finset.card_insert_of_notMem hvT, hTcard]
              · apply homogeneous_insert col T v true hmono
                intro x hx
                exact (Finset.mem_filter.mp (hT hx)).2
            · obtain ⟨T, hT, hTcard, hmono⟩ := h
              exact Or.inr ⟨T, hT.trans hRsub, hTcard, hmono⟩
          · have hB : 2 ^ (r + s + 1) ≤ B.card := by omega
            rcases his B (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB) with h | h
            · obtain ⟨T, hT, hTcard, hmono⟩ := h
              exact Or.inl ⟨T, hT.trans hBsub, hTcard, hmono⟩
            · obtain ⟨T, hT, hTcard, hmono⟩ := h
              have hvT : v ∉ T := by
                intro hmem
                exact (Finset.mem_erase.mp (Finset.mem_filter.mp (hT hmem)).1).1 rfl
              right
              refine ⟨insert v T, Finset.insert_subset hv (hT.trans hBsub), ?_, ?_⟩
              · simpa only [Finset.card_insert_of_notMem hvT, hTcard]
              · apply homogeneous_insert col T v false hmono
                intro x hx
                simpa using (Finset.mem_filter.mp (hT hx)).2

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, N ≤ 4 ^ k ∧
    ∀ (n : ℕ) (_ : N ≤ n) (col : Sym2 (Fin n) → Bool),
      (∃ S : Finset (Fin n), S.card = k ∧
        ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = true) ∨
      (∃ S : Finset (Fin n), S.card = k ∧
        ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = false) := by
  refine ⟨4 ^ k, le_rfl, ?_⟩
  intro n hn col
  have hpow : 2 ^ (k + k) = 4 ^ k := by
    rw [← two_mul, pow_mul]
    norm_num
  have hbound : 2 ^ (k + k) ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa only [hpow, Finset.card_univ, Fintype.card_fin] using hn
  rcases ramsey_card col k k Finset.univ hbound with h | h
  · obtain ⟨S, _, hcard, hmono⟩ := h
    exact Or.inl ⟨S, hcard, hmono⟩
  · obtain ⟨S, _, hcard, hmono⟩ := h
    exact Or.inr ⟨S, hcard, hmono⟩

#print axioms solution
