-- Prove2me | solution 1 for Cryptography.TernaryReversible.addRule_cycleBijective_of_exactlyOne
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:00:53.993731+00:00
-- url     : https://prove2.me/submissions/74f88701-cdf5-4d20-9d46-715c182e52f1

import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Additive
import Definitions.Def_Cryptography_TernaryReversible_Core
open Cryptography.TernaryReversible in
theorem solution {α β γ δ : Alph}
    (h : ExactlyOneNonzero α β γ) : CycleBijective (addRule α β γ δ) := by
  -- `s ↦ κ · (s ∘ σ) + δ` is bijective for an invertible `σ` and a unit `κ`
  have hgen : ∀ {n : ℕ} (σ τ : ZMod n → ZMod n), (∀ i, σ (τ i) = i) → (∀ i, τ (σ i) = i) →
      ∀ κ : Alph, κ ≠ 0 →
        Function.Bijective (fun (s : ZMod n → Alph) (i : ZMod n) => κ * s (σ i) + δ) := by
    intro n σ τ hστ hτσ κ hκ
    constructor
    · intro s s' hss
      funext j
      have := congrFun hss (τ j)
      simp only [hστ] at this
      exact mul_left_cancel₀ hκ (add_right_cancel this)
    · intro t
      refine ⟨fun j => κ⁻¹ * (t (τ j) - δ), ?_⟩
      funext i
      simp only [hτσ]
      rw [← mul_assoc, mul_inv_cancel₀ hκ, one_mul, sub_add_cancel]
  intro n _
  rcases h with ⟨hα, hβ, hγ⟩ | ⟨hα, hβ, hγ⟩ | ⟨hα, hβ, hγ⟩
  · -- only the left neighbour is read
    have := hgen (n := n) (fun i => i - 1) (fun i => i + 1) (fun i => by ring) (fun i => by ring) α hα
    convert this using 1
    funext s i
    simp only [globalMap, addRule, hβ, hγ, zero_mul, add_zero]
  · -- only the cell itself is read
    have := hgen (n := n) id id (fun _ => rfl) (fun _ => rfl) β hβ
    convert this using 1
    funext s i
    simp only [globalMap, addRule, hα, hγ, zero_mul, add_zero, zero_add, id]
  · -- only the right neighbour is read
    have := hgen (n := n) (fun i => i + 1) (fun i => i - 1) (fun i => by ring) (fun i => by ring) γ hγ
    convert this using 1
    funext s i
    simp only [globalMap, addRule, hα, hβ, zero_mul, add_zero, zero_add]
