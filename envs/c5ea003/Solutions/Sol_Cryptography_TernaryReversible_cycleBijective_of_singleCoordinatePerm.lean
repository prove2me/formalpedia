-- Prove2me | solution 1 for Cryptography.TernaryReversible.cycleBijective_of_singleCoordinatePerm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:05:47.906042+00:00
-- url     : https://prove2.me/submissions/b1820126-c6f9-4bc6-ad8c-ec8318645459

import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core
open Cryptography.TernaryReversible in
theorem solution {g : LocalRule}
    (hg : SingleCoordinatePerm g) : CycleBijective g := by
  -- `s ↦ e ∘ s ∘ σ` is bijective for an invertible `σ` and a permutation `e`
  have hgen : ∀ {n : ℕ} (σ τ : ZMod n → ZMod n), (∀ i, σ (τ i) = i) → (∀ i, τ (σ i) = i) →
      ∀ e : Equiv.Perm Alph,
        Function.Bijective (fun (s : ZMod n → Alph) (i : ZMod n) => e (s (σ i))) := by
    intro n σ τ hστ hτσ e
    constructor
    · intro s s' hss
      funext j
      have := congrFun hss (τ j)
      simp only [hστ] at this
      exact e.injective this
    · intro t
      refine ⟨fun j => e.symm (t (τ j)), ?_⟩
      funext i
      simp [hτσ]
  obtain ⟨e, he | he | he⟩ := hg <;> intro n _ <;> subst he
  · exact hgen (fun i => i - 1) (fun i => i + 1) (fun i => by ring) (fun i => by ring) e
  · exact hgen id id (fun _ => rfl) (fun _ => rfl) e
  · exact hgen (fun i => i + 1) (fun i => i - 1) (fun i => by ring) (fun i => by ring) e
