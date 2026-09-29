-- Prove2me | solution 2 for Bridges.InfiniteCubicMatchings.k4Chain_fanRaspaud
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:01:59.489614+00:00
-- url     : https://prove2.me/submissions/f252fdf0-2d97-4ed0-a18c-0b93a2cb0de6

import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
open Bridges.InfiniteCubicMatchings in
theorem solution : FanRaspaud k4Chain := by
  -- lift the three perfect matchings of `K₄` along the voltage
  have hinv : ∀ (i : Fin 3) (u : Fin 4), k4PM i (k4PM i u) = u := by decide
  have hvol : ∀ (i : Fin 3) (u : Fin 4), k4Vol u (k4PM i u) + k4Vol (k4PM i u) (k4PM i (k4PM i u)) = 0 := by
    decide
  let L : Fin 3 → PerfectMatching k4Chain := fun i =>
    { partner := fun p => (p.1 + k4Vol p.2 (k4PM i p.2), k4PM i p.2)
      isAdj := fun p => ⟨(k4Matching i).isAdj p.2, rfl⟩
      invol := fun p => by
        refine Prod.ext ?_ (hinv i p.2)
        simp only
        rw [add_assoc, hvol i p.2, add_zero] }
  -- lifts of different colour classes share no edge (project to `K₄`)
  have hdisj : ∀ e, e ∈ (L 0).edges → e ∉ (L 1).edges := by
    rintro e ⟨p, rfl⟩ ⟨q, hq⟩
    have h1 := congrArg (Sym2.map Prod.snd) hq
    simp only [Sym2.map_mk, L] at h1
    have key : ∀ u w : Fin 4, s(u, k4PM 0 u) ≠ s(w, k4PM 1 w) := by decide
    exact key _ _ h1
  refine ⟨L, ?_⟩
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h0, h1⟩, -⟩
  exact hdisj e h0 h1
