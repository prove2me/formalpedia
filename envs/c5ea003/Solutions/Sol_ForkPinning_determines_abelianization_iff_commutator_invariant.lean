-- Prove2me | solution 1 for ForkPinning.determines_abelianization_iff_commutator_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:13:36.206719+00:00
-- url     : https://prove2.me/submissions/00f8f81c-3060-43ee-8573-9392b71a0a05

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
open ForkPinning Finset Real in
theorem solution {G : Type*} [Group G] {β : Type*} (Y : G → β) :
    Determines (fun g : G => Abelianization.of g) Y ↔ ∀ g c, c ∈ commutator G → Y (g * c) = Y g := by
  constructor
  · intro hdet g c hc
    have hc1 : Abelianization.of c = 1 := by
      rw [← MonoidHom.mem_ker, Abelianization.ker_of]
      exact hc
    apply hdet
    simp only [map_mul, hc1, mul_one]
  · intro hinv g g' hg
    have hmem : g⁻¹ * g' ∈ commutator G := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      simp only [hg]
      simp
    have hY := hinv g (g⁻¹ * g') hmem
    rw [mul_inv_cancel_left] at hY
    exact hY.symm
