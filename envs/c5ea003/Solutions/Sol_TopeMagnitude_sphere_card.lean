-- Prove2me | solution 1 for TopeMagnitude.sphere_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:50:36.792018+00:00
-- url     : https://prove2.me/submissions/7d2cf201-462b-4eae-8b77-494fbfe2bd32

import Mathlib
import Definitions.Def_Geometry_FlagComplex
import Definitions.Def_Geometry_TopeMagnitude_Hypercube
open TopeMagnitude in
theorem solution {n k : ℕ} (x : Fin n → Bool) :
    Fintype.card (sphere x k) = n.choose k := by
  classical
  -- flipping exactly the coordinates in `s` separates `x` from the result along `s`
  have hsep : ∀ s : Finset (Fin n), separatingWalls x (flip x s) = s := by
    intro s
    ext i
    by_cases hi : i ∈ s <;> cases hx : x i <;> simp [separatingWalls, TopeMagnitude.flip, hi, hx]
  -- chambers at distance `k` ↔ `k`-subsets of walls
  let e : sphere x k ≃ {s : Finset (Fin n) // s.card = k} :=
    { toFun := fun y => ⟨separatingWalls x y.1, y.2⟩
      invFun := fun s => ⟨flip x s.1, by
        show (separatingWalls x (flip x s.1)).card = k
        rw [hsep, s.2]⟩
      left_inv := fun y => by
        apply Subtype.ext
        funext i
        show flip x (separatingWalls x y.1) i = y.1 i
        by_cases h : x i = y.1 i
        · simp [TopeMagnitude.flip, separatingWalls, h]
        · have : (!x i) = y.1 i := by
            cases hx : x i <;> cases hy : y.1 i <;> simp_all
          simp [TopeMagnitude.flip, separatingWalls, h, this]
      right_inv := fun s => by
        apply Subtype.ext
        exact hsep s.1 }
  rw [Fintype.card_congr e, Fintype.card_finset_len, Fintype.card_fin]
