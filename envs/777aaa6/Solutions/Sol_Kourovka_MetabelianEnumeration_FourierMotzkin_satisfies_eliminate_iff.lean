-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.satisfies_eliminate_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:23.01967+00:00
-- url     : https://prove2.me/submissions/a6735350-e2bc-4d50-9a03-3f61dbb188e5

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution {n : ℕ} (rows : List (Row (n + 1)))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : Fin n → K) :
    Satisfies (eliminate rows) x ↔
      (∀ r ∈ rows, r.head = 0 → r.tail.eval x ≤ 0) ∧
      (∀ l ∈ rows, l.head < 0 → ∀ u ∈ rows, 0 < u.head →
        (l.combine u).eval x ≤ 0) := by
  constructor
  · intro h
    constructor
    · intro r hr hz
      apply h _
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa⟩, rfl⟩
    · intro l hl hneg u hu hpos
      apply h _
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨l, List.mem_filter.mpr ⟨hl, by simpa⟩,
        List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu, by simpa⟩, rfl⟩⟩
  · rintro ⟨hz, hp⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hsmem, hsz⟩ := List.mem_filter.mp hs
      exact hz s hsmem (of_decide_eq_true hsz)
    · obtain ⟨l, hl, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hlmem, hlneg⟩ := List.mem_filter.mp hl
      obtain ⟨humem, hupos⟩ := List.mem_filter.mp hu
      exact hp l hlmem (of_decide_eq_true hlneg) u humem (of_decide_eq_true hupos)
end Kourovka.MetabelianEnumeration.FourierMotzkin
