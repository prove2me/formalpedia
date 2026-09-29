-- Prove2me | solution 1 for TropicalLA.charCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:41:29.700754+00:00
-- url     : https://prove2.me/submissions/d893146e-04df-41a0-a909-8532fc2940f4

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCharPoly
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue

open TropicalLA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (A : Matrix ι ι ℝ) : charCoeff A 0 = 0 := by
  dsimp [charCoeff]
  split_ifs with hne
  · have hz : ∀ p ∈ admPairs ι 0, minorWeight A p.1 p.2 = 0 := by
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hs : p.1 = ∅ := Finset.card_eq_zero.mp hp'.1
      simp [minorWeight, hs]
    refine le_antisymm ?top ?bot
    case top =>
      exact Finset.sup'_le hne (fun q => minorWeight A q.1 q.2)
        (fun p hp => (hz p hp).le)
    case bot =>
      obtain ⟨p, hp⟩ := hne
      have hle :=
        Finset.le_sup' (f := fun q : Finset ι × Equiv.Perm ι => minorWeight A q.1 q.2) hp
      -- hle : minorWeight A p.1 p.2 ≤ sup'
      simpa [hz p hp] using hle
  · rfl
