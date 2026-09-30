-- Prove2me | solution 1 for sumfree_set_density
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:05.307286+00:00
-- url     : https://prove2.me/submissions/30cbe1ff-5e7a-4ecc-bd45-e069bf549145

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith

private theorem sumFree_twice_card_le {n : ℕ} (A : Finset (Fin n))
    (hA : ∀ a b c : Fin n, a ∈ A → b ∈ A → c ∈ A →
      a.val + b.val ≠ c.val) : 2 * A.card ≤ n := by
  classical
  by_cases hne : A.Nonempty
  · let b := A.max' hne
    have hb : b ∈ A := A.max'_mem hne
    have hmax (a : Fin n) (ha : a ∈ A) : a.val ≤ b.val := A.le_max' a ha
    let S : Finset ℕ := A.image Fin.val
    let T : Finset ℕ := A.image (fun a => b.val - a.val)
    have hcardS : S.card = A.card := Finset.card_image_of_injective A Fin.val_injective
    have hcardT : T.card = A.card := by
      apply Finset.card_image_of_injOn
      intro a ha c hc heq
      apply Fin.ext
      change b.val - a.val = b.val - c.val at heq
      have ha_le := hmax a ha
      have hc_le := hmax c hc
      omega
    have hdisjoint : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxT
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxS
      obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hxT
      have hc_le := hmax c hc
      exact hA a c b ha hc hb (by omega)
    have hsubset : S ∪ T ⊆ Finset.range n := by
      intro x hx
      apply Finset.mem_range.mpr
      rcases Finset.mem_union.mp hx with hxS | hxT
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxS
        exact a.isLt
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxT
        exact lt_of_le_of_lt (Nat.sub_le _ _) b.isLt
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_union_of_disjoint hdisjoint, hcardS, hcardT,
      Finset.card_range] at hcard
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

theorem solution :
    ∀ eps : ℝ, 0 < eps →
    ∀ (n : ℕ) (A : Finset (Fin n)),
      (∀ a b c : Fin n, a ∈ A → b ∈ A → c ∈ A →
        a.val + b.val ≠ c.val) →
      (A.card : ℝ) ≤ (n : ℝ) / 2 + eps := by
  intro eps heps n A hA
  have hbound : (2 : ℝ) * A.card ≤ n := by
    exact_mod_cast sumFree_twice_card_le A hA
  linarith

#print axioms solution
