-- Prove2me | solution 1 for ReversibleElementary.six_rules_universally_reversible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:06:47.300442+00:00
-- url     : https://prove2.me/submissions/7bae2957-17f8-4c13-b655-c8925be1ade9

import Mathlib
import Definitions.Def_Novelty_ReversibleElementary
open ReversibleElementary in
theorem solution :
    ∀ w ∈ ([15, 51, 85, 170, 204, 240] : List (Fin 256)), UniversallyReversible w := by
  -- `b ∘ x ∘ σ` is a bijection of configurations when `σ` and `b` are invertible
  have hbij : ∀ {n : ℕ} (σ τ : Fin n → Fin n), (∀ i, σ (τ i) = i) → (∀ i, τ (σ i) = i) →
      ∀ b : Bool → Bool, (∀ v, b (b v) = v) →
        Function.Bijective (fun (x : Fin n → Bool) (i : Fin n) => b (x (σ i))) := by
    intro n σ τ hστ hτσ b hb
    constructor
    · intro x y hxy
      funext j
      have := congrFun hxy (τ j)
      simp only [hστ] at this
      rw [← hb (x j), this, hb]
    · intro z
      refine ⟨fun j => b (z (τ j)), ?_⟩
      funext i
      simp only [hτσ, hb]
  -- the cyclic shifts are mutually inverse
  have hRL : ∀ {n : ℕ} (hn : 0 < n) (i : Fin n), rightIdx hn (leftIdx hn i) = i := by
    intro n hn i
    apply Fin.ext
    simp only [rightIdx, leftIdx]
    rcases Nat.eq_zero_or_pos i.val with h | h
    · rw [h, zero_add, Nat.mod_eq_of_lt (show n - 1 < n by omega), Nat.sub_add_cancel hn,
        Nat.mod_self]
    · rw [show i.val + n - 1 = (i.val - 1) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show i.val - 1 < n by omega), Nat.sub_add_cancel h,
        Nat.mod_eq_of_lt i.isLt]
  have hLR : ∀ {n : ℕ} (hn : 0 < n) (i : Fin n), leftIdx hn (rightIdx hn i) = i := by
    intro n hn i
    apply Fin.ext
    simp only [rightIdx, leftIdx]
    rcases Nat.lt_or_ge (i.val + 1) n with h | h
    · rw [Nat.mod_eq_of_lt h, show i.val + 1 + n - 1 = i.val + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt i.isLt]
    · have hi : i.val + 1 = n := by have := i.isLt; omega
      rw [hi, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
  have hid : ∀ v : Bool, id (id v) = v := fun _ => rfl
  have hnot : ∀ v : Bool, (!(!v)) = v := Bool.not_not
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  intro n hn
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · -- rule 15: `¬ left`
    have hr : ∀ l c r, wolframRule 15 l c r = !l := by decide
    have := hbij (leftIdx hn) (rightIdx hn) (hLR hn) (hRL hn) (fun v => !v) hnot
    convert this using 1
    funext x i
    simp only [globalMap, hr]
  · -- rule 51: `¬ centre`
    have hr : ∀ l c r, wolframRule 51 l c r = !c := by decide
    have := hbij (n := n) id id (fun _ => rfl) (fun _ => rfl) (fun v => !v) hnot
    convert this using 1
    funext x i
    simp only [globalMap, hr, id]
  · -- rule 85: `¬ right`
    have hr : ∀ l c r, wolframRule 85 l c r = !r := by decide
    have := hbij (rightIdx hn) (leftIdx hn) (hRL hn) (hLR hn) (fun v => !v) hnot
    convert this using 1
    funext x i
    simp only [globalMap, hr]
  · -- rule 170: `right`
    have hr : ∀ l c r, wolframRule 170 l c r = r := by decide
    have := hbij (rightIdx hn) (leftIdx hn) (hRL hn) (hLR hn) id hid
    convert this using 1
    funext x i
    simp only [globalMap, hr, id]
  · -- rule 204: `centre`
    have hr : ∀ l c r, wolframRule 204 l c r = c := by decide
    have := hbij (n := n) id id (fun _ => rfl) (fun _ => rfl) id hid
    convert this using 1
    funext x i
    simp only [globalMap, hr, id]
  · -- rule 240: `left`
    have hr : ∀ l c r, wolframRule 240 l c r = l := by decide
    have := hbij (leftIdx hn) (rightIdx hn) (hLR hn) (hRL hn) id hid
    convert this using 1
    funext x i
    simp only [globalMap, hr, id]
