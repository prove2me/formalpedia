-- Prove2me | solution 1 for lean_workbook_plus_9744
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:13:16.735685+00:00
-- url     : https://prove2.me/submissions/5f8c380d-ce93-4d59-bbc3-24df6fce87a4

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

namespace FourDistinctSums

def NoFour (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + c = b + d →
    a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d

def pairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  S.offDiag.filter (fun p => p.1 < p.2)

theorem mem_pairs (S : Finset ℕ) (a b : ℕ) :
    (a, b) ∈ pairs S ↔ a ∈ S ∧ b ∈ S ∧ a < b := by
  simp only [pairs, Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨ha, hb, _⟩, hlt⟩
    exact ⟨ha, hb, hlt⟩
  · rintro ⟨ha, hb, hlt⟩
    exact ⟨⟨ha, hb, Nat.ne_of_lt hlt⟩, hlt⟩

theorem pair_count (S : Finset ℕ) :
    2 * (pairs S).card = S.card * S.card - S.card := by
  have he : (S.offDiag.filter (fun p => ¬ p.1 < p.2)).card = (pairs S).card := by
    apply Finset.card_bij (fun p _ => p.swap)
    · intro p hp
      rcases p with ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag] at hp
      change (b, a) ∈ pairs S
      rw [mem_pairs]
      exact ⟨hp.1.2.1, hp.1.1, by omega⟩
    · intro p hp q hq he
      exact Prod.swap_injective he
    · intro p hp
      rcases p with ⟨a, b⟩
      rw [mem_pairs] at hp
      refine ⟨(b, a), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      exact ⟨⟨hp.2.1, hp.1, by omega⟩, by omega⟩
  have hc := S.offDiag.card_filter_add_card_filter_not (fun p => p.1 < p.2)
  rw [he, Finset.offDiag_card] at hc
  change (pairs S).card + (pairs S).card = _ at hc
  omega

theorem difference_collision (S : Finset ℕ) (hS : NoFour S)
    (a b c d : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a < b) (hcd : c < d) (he : b - a = d - c) :
    (a = c ∧ b = d) ∨ b = c ∨ d = a := by
  have hf := hS a ha b hb d hd c hc (by omega)
  omega

theorem midpoint_collision (S : Finset ℕ) (hS : NoFour S)
    (a b d : ℕ) (hb : b ∈ S) (hd : d ∈ S) (hab : a < b) (had : a < d)
    (hp : ∃ c ∈ S, c + b = 2 * a) (hq : ∃ e ∈ S, e + d = 2 * a) : b = d := by
  obtain ⟨c, hc, hcp⟩ := hp
  obtain ⟨e, he, heq⟩ := hq
  have hf := hS c hc e he b hb d hd (by omega)
  omega

noncomputable def code (S : Finset ℕ) (p : ℕ × ℕ) : ℕ ⊕ ℕ := by
  classical
  exact if ∃ c ∈ S, c + p.2 = 2 * p.1 then Sum.inr p.1
    else Sum.inl (p.2 - p.1 - 1)

theorem code_injective (S : Finset ℕ) (hS : NoFour S) :
    Set.InjOn (code S) (pairs S) := by
  classical
  rintro ⟨a, b⟩ hp ⟨c, d⟩ hq he
  change (a, b) ∈ pairs S at hp
  change (c, d) ∈ pairs S at hq
  rw [mem_pairs] at hp hq
  by_cases hu : ∃ e ∈ S, e + b = 2 * a
  · by_cases hv : ∃ e ∈ S, e + d = 2 * c
    · simp only [code, hu, hv, ↓reduceIte, Sum.inr.injEq] at he
      subst c
      have hbd := midpoint_collision S hS a b d hp.2.1 hq.2.1 hp.2.2 hq.2.2 hu hv
      exact Prod.ext rfl hbd
    · simp [code, hu, hv] at he
  · by_cases hv : ∃ e ∈ S, e + d = 2 * c
    · simp [code, hu, hv] at he
    · simp only [code, hu, hv, ↓reduceIte, Sum.inl.injEq] at he
      have hf := difference_collision S hS a b c d hp.1 hp.2.1 hq.1 hq.2.1
        hp.2.2 hq.2.2 (by omega)
      rcases hf with ⟨hac, hbd⟩ | hbc | hda
      · exact Prod.ext hac hbd
      · exact False.elim (hv ⟨a, hp.1, by omega⟩)
      · exact False.elim (hu ⟨c, hq.1, by omega⟩)

theorem interval_bound (S : Finset ℕ) (L U : ℕ)
    (hL : ∀ a ∈ S, L ≤ a) (hU : ∀ a ∈ S, a ≤ U) (hS : NoFour S) :
    S.card * S.card - S.card ≤ 2 * ((U - L) + S.card) := by
  classical
  have hm : ∀ p ∈ pairs S, code S p ∈ (Finset.range (U - L)).disjSum S := by
    rintro ⟨a, b⟩ hp
    rw [mem_pairs] at hp
    by_cases hu : ∃ c ∈ S, c + b = 2 * a
    · simpa [code, hu] using hp.1
    · have hbnd : b - a - 1 < U - L := by
        have ha := hL a hp.1
        have hb := hU b hp.2.1
        omega
      simpa [code, hu] using hbnd
  have hc := Finset.card_le_card_of_injOn (code S) hm (code_injective S hS)
  rw [Finset.card_disjSum, Finset.card_range] at hc
  rw [← pair_count S]
  omega

theorem threshold (S : Finset ℕ) (L U : ℕ)
    (hL : ∀ a ∈ S, L ≤ a) (hU : ∀ a ∈ S, a ≤ U)
    (hcard : 2 * ((U - L) + S.card) < S.card * S.card - S.card) :
    ∃ a b c d : ℕ, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ a + c = b + d := by
  by_contra hn
  have hS : NoFour S := by
    intro a ha b hb c hc d hd he
    by_contra hne
    apply hn
    exact ⟨a, b, c, d, ha, hb, hc, hd, by tauto⟩
  exact (not_lt_of_ge (interval_bound S L U hL hU hS)) hcard

theorem four_distinct (S : Finset ℕ) (hcard : S.card = 16)
    (hbound : ∀ a ∈ S, a ≤ 100) :
    ∃ a b c d : ℕ, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ a + c = b + d := by
  exact threshold S 0 100 (fun _ _ => Nat.zero_le _) hbound (by norm_num [hcard])

end FourDistinctSums

theorem solution (A : Finset ℕ) (hA : A.card = 16) (hA' : ∀ a ∈ A, a ≤ 100) :
    ∃ a b c d : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A ∧ a + c = b + d := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd, he⟩ :=
    FourDistinctSums.four_distinct A hA hA'
  exact ⟨a, b, c, d, ha, hb, hc, hd, he⟩
