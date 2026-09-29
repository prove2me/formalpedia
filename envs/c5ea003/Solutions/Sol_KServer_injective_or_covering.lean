-- Prove2me | solution 1 for KServer.injective_or_covering
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:35:55.293943+00:00
-- url     : https://prove2.me/submissions/f287c953-ca3d-4f87-a00f-e0eb652b5ead

import Mathlib
import Definitions.Def_KServer_model

open KServer

/-- On any type, either `k` servers can be placed on `k` distinct points, or they can be
placed so as to cover every point. -/
theorem solution (k : ℕ) (M : Type) (C₀ : Config k M) :
    (∃ X : Config k M, Function.Injective X) ∨
      (∃ Y : Config k M, ∀ x : M, ∃ i, Y i = x) := by
  classical
  induction k with
  | zero => exact Or.inl ⟨C₀, fun a _ _ => a.elim0⟩
  | succ k ih =>
      rcases ih (fun i => C₀ i.castSucc) with ⟨g, hg⟩ | ⟨g, hg⟩
      · by_cases hx : ∃ x : M, ∀ i, g i ≠ x
        · obtain ⟨x, hx⟩ := hx
          refine Or.inl ⟨Fin.snoc g x, ?_⟩
          intro a b hab
          induction a using Fin.lastCases with
          | last =>
              induction b using Fin.lastCases with
              | last => rfl
              | cast j =>
                  rw [Fin.snoc_last, Fin.snoc_castSucc] at hab
                  exact absurd hab.symm (hx j)
          | cast i =>
              induction b using Fin.lastCases with
              | last =>
                  rw [Fin.snoc_last, Fin.snoc_castSucc] at hab
                  exact absurd hab (hx i)
              | cast j =>
                  rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hab
                  rw [hg hab]
        · push_neg at hx
          refine Or.inr ⟨Fin.snoc g (C₀ 0), fun x => ?_⟩
          obtain ⟨i, hi⟩ := hx x
          exact ⟨i.castSucc, by rw [Fin.snoc_castSucc]; exact hi⟩
      · refine Or.inr ⟨Fin.snoc g (C₀ 0), fun x => ?_⟩
        obtain ⟨i, hi⟩ := hg x
        exact ⟨i.castSucc, by rw [Fin.snoc_castSucc]; exact hi⟩
