-- Prove2me | solution 1 for Novelty.Catalog.Novelty.FriendshipChromaticPolynomial.friendship_chromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:12:30.498578+00:00
-- url     : https://prove2.me/submissions/41754132-12af-49de-81c0-0172f7d0c6a9

import Mathlib
import Definitions.Def_Novelty_FriendshipChromaticPolynomial
open Catalog.Novelty.FriendshipChromaticPolynomial in
theorem solution {n : ℕ} (hn : 1 ≤ n) : (friendship n).chromaticNumber = 3 := by
  -- three colours suffice: hub `0`, blade ends `1` and `2`
  have hcol : (friendship n).Colorable 3 := by
    -- the hub gets colour 0; each blade's two ends get colours 1 and 2
    let c : Option (Fin n × Bool) → Fin 3 := fun v =>
      match v with
      | none => 0
      | some (_, false) => 1
      | some (_, true) => 2
    refine ⟨SimpleGraph.Coloring.mk c ?_⟩
    intro v w hvw
    rcases v with _ | ⟨i, _ | _⟩ <;> rcases w with _ | ⟨j, _ | _⟩ <;>
      simp_all [friendship, frAdj, c]
  apply le_antisymm hcol.chromaticNumber_le
  -- two colours do not: the hub and the two ends of the first blade form a triangle
  by_contra hlt
  push Not at hlt
  have h2 : (friendship n).chromaticNumber ≤ 2 := Order.le_of_lt_succ hlt
  obtain ⟨c⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp h2
  let i : Fin n := ⟨0, hn⟩
  have h1 := c.valid (show (friendship n).Adj none (some (i, false)) by simp [friendship, frAdj])
  have h2 := c.valid (show (friendship n).Adj none (some (i, true)) by simp [friendship, frAdj])
  have h3 := c.valid (show (friendship n).Adj (some (i, false)) (some (i, true)) by
    simp [friendship, frAdj])
  revert h1 h2 h3
  generalize c none = a
  generalize c (some (i, false)) = b
  generalize c (some (i, true)) = d
  revert a b d
  decide
