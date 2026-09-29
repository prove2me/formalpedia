-- Prove2me | solution 1 for motivic_density_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:19:24.091463+00:00
-- url     : https://prove2.me/submissions/12a0d45a-24d8-4c7d-b6f2-cd9d4a8ea65d

-- Sol generated from Bridges/NeuralCoding/Bridge9_Motivic.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_Bridge9_Motivic

/-! # CatalogBuild.Speculative.RosettaStone.Bridge9_Motivic

Auto-generated from theorem catalog database.
Domain: Speculative/RosettaStone
Declarations: 18
-/

noncomputable section




















theorem solution:
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ g : ℕ, N ≤ g → curve_motivic_density g < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ g : ℝ, N ≤ g → 3 / (2 * g + 2) < ε := by
    exact ⟨ 3 / ε + 1, fun g hg => by rw [ div_lt_iff₀ ] <;> nlinarith [ show ( 0 : ℝ ) < ε by positivity, div_mul_cancel₀ 3 ( show ( ε : ℝ ) ≠ 0 by positivity ) ] ⟩;
  obtain ⟨N', hN'⟩ : ∃ N' : ℕ, ∀ g : ℕ, N' ≤ g → (3 : ℝ) / (2 * g + 2) < ε := by
    exact ⟨ ⌈N⌉₊, fun g hg => hN g <| Nat.le_of_ceil_le hg ⟩;
  use N';
  intro g hg
  specialize hN' g hg
  have h_cast : (3 : ℝ) / (2 * g + 2) = (curve_motivic_density g : ℝ) := by
    unfold curve_motivic_density; push_cast; ring;
  exact_mod_cast h_cast ▸ hN'
