-- Prove2me | solution 1 for Graph.TwinWidth.starSequence_pairs_ne
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:40:04.844163+00:00
-- url     : https://prove2.me/submissions/aa1e4212-a600-4305-a687-d129217053ec

import Mathlib
import Definitions.Def_Geometry_Contractions
open Graph.TwinWidth in
theorem solution {V : Type*} {l : List V} (h : l.Nodup) :
    ∀ e ∈ starSequence l, e.1 ≠ e.2 := by
  cases l with
  | nil => intro e he; simp [starSequence] at he
  | cons v₀ rest =>
    -- every pair is `(v₀, v)` with `v` later in the list, and `v₀` does not recur
    intro e he
    simp only [starSequence, List.mem_map] at he
    obtain ⟨v, hv, rfl⟩ := he
    rw [List.nodup_cons] at h
    intro hv₀
    have hv₀' : v₀ = v := hv₀
    exact h.1 (hv₀' ▸ hv)
