-- Prove2me | solution 1 for SelfModifyingResearch.bounded_reflection_eventually_fixed_and_converges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T20:19:08.742697+00:00
-- url     : https://prove2.me/submissions/39501d52-a1ea-4903-9583-c82ba3fd2cec

import Mathlib
import Definitions.Def_Logic_SelfModifyingResearchConnector
open Filter Topology SelfModifyingResearch in
theorem solution (S : System) (R : Run S)
    [TopologicalSpace S.Cycle] [DiscreteTopology S.Cycle] :
    ∃ N : ℕ,
      (∀ n, N ≤ n → R.cycle n = R.cycle N) ∧
      Tendsto R.cycle atTop (𝓝 (R.cycle N)) := by
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
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty (fun n => S.quality (R.cycle n))) hbdd
  -- after the plateau time every revision is a fixed point, so the run is constant
  have hfix : ∀ n, N ≤ n → R.cycle (n + 1) = R.cycle n := by
    intro n hn
    rw [R.evolves n]
    apply S.plateau_fixed
    have h1 : S.quality (R.cycle (n + 1)) ≤ sSup (Set.range (fun n => S.quality (R.cycle n))) :=
      le_csSup hbdd ⟨n + 1, rfl⟩
    have h2 : S.quality (R.cycle N) ≤ S.quality (R.cycle n) := hmono hn
    have h3 := hstep n
    simp only at hN
    rw [← R.evolves n]
    omega
  have hconst : ∀ n, N ≤ n → R.cycle n = R.cycle N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [hfix n hn, ih]
  refine ⟨N, hconst, ?_⟩
  exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => (hconst n hn).symm⟩)
