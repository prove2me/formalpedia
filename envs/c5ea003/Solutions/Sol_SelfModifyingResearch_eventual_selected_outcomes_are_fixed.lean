-- Prove2me | solution 1 for SelfModifyingResearch.eventual_selected_outcomes_are_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:25:42.012762+00:00
-- url     : https://prove2.me/submissions/6183b8c6-0dc7-4a20-8bac-bca29c22baaf

import Mathlib
import Definitions.Def_Logic_SelfModifyingResearchConnector
open Filter Topology SelfModifyingResearch in
theorem solution (S : System) (R : Run S) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      S.revise (R.cycle n) (R.outcome n) = R.cycle n := by
  -- quality along the run is monotone and bounded by the capacity
  have hstep : ∀ n, S.quality (R.cycle n) ≤ S.quality (R.cycle (n + 1)) := by
    intro n
    rw [R.evolves n]
    exact S.improves _ _
  have hmono : Monotone (fun n => S.quality (R.cycle n)) := monotone_nat_of_le_succ hstep
  have hbdd : BddAbove (Set.range (fun n => S.quality (R.cycle n))) :=
    ⟨S.capacity, by
      rintro _ ⟨n, rfl⟩
      exact S.qualityBound _⟩
  -- it attains its supremum at some time `N`, after which it is constant
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty (fun n => S.quality (R.cycle n))) hbdd
  refine ⟨N, fun n hn => ?_⟩
  apply S.plateau_fixed
  have h1 : S.quality (R.cycle (n + 1)) ≤ sSup (Set.range (fun n => S.quality (R.cycle n))) :=
    le_csSup hbdd ⟨n + 1, rfl⟩
  have h2 : S.quality (R.cycle N) ≤ S.quality (R.cycle n) := hmono hn
  have h3 := hstep n
  simp only at hN
  rw [← R.evolves n]
  omega
