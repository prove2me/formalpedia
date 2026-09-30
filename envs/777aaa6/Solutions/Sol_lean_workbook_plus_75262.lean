-- Prove2me | solution 1 for lean_workbook_plus_75262
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:18:47.989938+00:00
-- url     : https://prove2.me/submissions/1b0eabb5-8e8b-4d0c-9531-93e1374b818e

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

private theorem nontrivial_collision (A : Finset ℕ) (hA : A.card = 16)
    (hA2 : ∀ a ∈ A, a ≤ 100) :
    ∃ a b c d : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A ∧
      a ≠ b ∧ a ≠ d ∧ a + c = b + d := by
  classical
  let color : A.offDiag → Fin 201 := fun p => ⟨p.val.1 + 100 - p.val.2, by
    have hp := Finset.mem_offDiag.mp p.property
    have ha := hA2 p.val.1 hp.1
    omega⟩
  have hnot : ¬Function.Injective color := by
    intro hinj
    have hcard := Fintype.card_le_of_injective color hinj
    simp only [Fintype.card_coe, Fintype.card_fin, Finset.offDiag_card, hA] at hcard
    norm_num at hcard
  unfold Function.Injective at hnot
  push_neg at hnot
  obtain ⟨p, q, heq, hne⟩ := hnot
  have hp := Finset.mem_offDiag.mp p.property
  have hq := Finset.mem_offDiag.mp q.property
  have hb := hA2 p.val.2 hp.2.1
  have hd := hA2 q.val.2 hq.2.1
  have hdiff : p.val.1 + 100 - p.val.2 = q.val.1 + 100 - q.val.2 :=
    congrArg Fin.val heq
  have hsum : p.val.1 + q.val.2 = p.val.2 + q.val.1 := by omega
  have hfirst : p.val.1 ≠ q.val.1 := by
    intro h
    have hsecond : p.val.2 = q.val.2 := by omega
    exact hne (Subtype.ext (Prod.ext h hsecond))
  exact ⟨p.val.1, p.val.2, q.val.2, q.val.1,
    hp.1, hp.2.1, hq.2.1, hq.1, hp.2.2, hfirst, hsum⟩

theorem solution (A : Finset ℕ) (hA : A.card = 16) (hA2 : ∀ a ∈ A, a ≤ 100) :
    ∃ a b c d : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A ∧ a + c = b + d := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, _, _, heq⟩ := nontrivial_collision A hA hA2
  exact ⟨a, b, c, d, ha, hb, hc, hd, heq⟩
