-- Prove2me | solution 1 for range_bound_from_bounded_diff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:31:35.455201+00:00
-- url     : https://prove2.me/submissions/f25dcd92-e695-4f40-bf9d-22fbf8078cde

import Mathlib
import Definitions.Def_Bridges_NeuralCoding_TropicalSpectralConcentration
theorem solution (m : ℕ) (f : (Fin m → Bool) → ℤ)
    (c : ℕ) (hbd : ∀ (x : Fin m → Bool) (i : Fin m) (b : Bool),
      |f x - f (Function.update x i b)| ≤ c) :
    ∀ x y : Fin m → Bool, |f x - f y| ≤ m * c := by
  intro x y
  -- hybrids: `y` on coordinates below `k`, `x` elsewhere
  let z : ℕ → (Fin m → Bool) := fun k i => if i.val < k then y i else x i
  have hz0 : z 0 = x := by funext i; simp [z]
  have hzm : z m = y := by funext i; simp [z, i.2]
  have hstep : ∀ k (hk : k < m), z (k + 1) = Function.update (z k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
    intro k hk
    funext i
    by_cases hi : i = ⟨k, hk⟩
    · subst hi
      simp [z]
    · have hik : i.val ≠ k := fun h => hi (Fin.ext h)
      rw [Function.update_of_ne hi]
      simp only [z]
      by_cases hlt : i.val < k
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]
  -- each hybrid step moves `f` by at most `c`
  have hind : ∀ k, k ≤ m → |f x - f (z k)| ≤ k * c := by
    intro k
    induction k with
    | zero => intro _; rw [hz0]; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hbd (z k) ⟨k, by omega⟩ (y ⟨k, by omega⟩)
      rw [← hstep k (by omega)] at h2
      calc |f x - f (z (k + 1))| = |(f x - f (z k)) + (f (z k) - f (z (k + 1)))| := by ring_nf
        _ ≤ |f x - f (z k)| + |f (z k) - f (z (k + 1))| := abs_add_le _ _
        _ ≤ k * c + c := add_le_add h1 h2
        _ = ((k + 1 : ℕ) : ℤ) * c := by push_cast; ring
  have := hind m le_rfl
  rwa [hzm] at this
