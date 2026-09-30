-- Prove2me | solution 1 for lean_workbook_plus_7445
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:05:37.567848+00:00
-- url     : https://prove2.me/submissions/3dbc20a7-420c-4d74-8ed7-277997b31bf7

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

private theorem ordered_congruent_pair (n : ℕ) (hn : 0 < n) (S : Finset ℤ)
    (hS : n < S.card) :
    ∃ a b : ℤ, a ∈ S ∧ b ∈ S ∧ a < b ∧ (n : ℤ) ∣ b - a := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let residue : S → ZMod n := fun x => x.val
  have hnot : ¬ Function.Injective residue := by
    intro hinj
    have hcard := Fintype.card_le_of_injective residue hinj
    have : S.card ≤ n := by simpa using hcard
    omega
  unfold Function.Injective at hnot
  push_neg at hnot
  obtain ⟨x, y, heq, hne⟩ := hnot
  change (x.val : ZMod n) = (y.val : ZMod n) at heq
  have hval : x.val ≠ y.val := fun h => hne (Subtype.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hlt
  · exact ⟨x.val, y.val, x.property, y.property, hlt,
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp heq⟩
  · exact ⟨y.val, x.val, y.property, x.property, hlt,
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp heq.symm⟩

theorem solution (S : Finset ℤ) (hS : S.card = 18) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ a - b ≡ 0 [ZMOD 17] := by
  obtain ⟨a, b, ha, hb, _, hd⟩ := ordered_congruent_pair 17 (by decide) S (by omega)
  exact ⟨b, a, hb, ha, Int.modEq_zero_iff_dvd.mpr hd⟩
