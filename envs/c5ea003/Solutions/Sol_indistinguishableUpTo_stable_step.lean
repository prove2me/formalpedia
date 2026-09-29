-- Prove2me | solution 1 for indistinguishableUpTo_stable_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:58:12.993546+00:00
-- url     : https://prove2.me/submissions/9cfaecba-f889-4688-95e6-e5f87174f544

import Mathlib
import Definitions.Def_Bridges_NeuralCoding_AlgebraEMLClosureComputation
universe u v w
theorem solution {σ : Type u} {α : Type v} {K : Type w} [Semiring K]
    (M : ClosureSemimoduleSystem σ α K) (P : ProbeFamily σ K) (n : ℕ)
    (hStab : ∀ s t : σ, IndistinguishableUpTo M P n s t →
              IndistinguishableUpTo M P (n + 1) s t) :
    ∀ k : ℕ, ∀ s t : σ, IndistinguishableUpTo M P n s t →
      IndistinguishableUpTo M P (n + k) s t := by
  -- reading a first letter moves to the successor state
  have hcons : ∀ (s : σ) (a : α) (w : List α),
      ClosureTrace M P s (a :: w) = ClosureTrace M P (M.step s a) w := fun s a w => rfl
  -- `(n+1)`-indistinguishable states have `n`-indistinguishable successors
  have hsucc : ∀ (s t : σ) (a : α), IndistinguishableUpTo M P (n + 1) s t →
      IndistinguishableUpTo M P n (M.step s a) (M.step t a) := by
    intro s t a h w hw
    rw [← hcons, ← hcons]
    exact h (a :: w) (by simp; omega)
  intro k
  induction k with
  | zero =>
    intro s t h
    simpa using h
  | succ k ih =>
    intro s t h w hw
    rcases Nat.lt_or_ge w.length (n + k + 1) with hlt | hge
    · exact ih s t h w (by omega)
    · cases w with
      | nil => simp at hge
      | cons a w' =>
        rw [hcons, hcons]
        simp only [List.length_cons] at hw
        exact ih _ _ (hsucc s t a (hStab s t h)) w' (by omega)
