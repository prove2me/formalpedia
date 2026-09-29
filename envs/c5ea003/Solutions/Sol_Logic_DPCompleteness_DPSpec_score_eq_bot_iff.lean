-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.score_eq_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:07:06.037292+00:00
-- url     : https://prove2.me/submissions/4ebfa3e3-da28-4082-b1a4-2a7166dae696

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessConstrained
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] (D : DPSpec S (WithBot W)) (f : ℕ → S) :
    ∀ n : ℕ, D.score f n = ⊥ ↔
      (D.init (f 0) = ⊥ ∨ ∃ i < n, D.step i (f i) (f (i + 1)) = ⊥) := by
  intro n
  induction n with
  | zero =>
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | ⟨i, hi, -⟩)
      · exact h
      · omega
  | succ n ih =>
    show D.score f n + D.step n (f n) (f (n + 1)) = ⊥ ↔ _
    rw [WithBot.add_eq_bot, ih]
    constructor
    · rintro ((h | ⟨i, hi, hbot⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, hbot⟩
      · exact Or.inr ⟨n, by omega, h⟩
    · rintro (h | ⟨i, hi, hbot⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact Or.inl (Or.inr ⟨i, hlt, hbot⟩)
        · subst heq
          exact Or.inr hbot
