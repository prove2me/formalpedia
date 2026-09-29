-- Prove2me | solution 1 for AlmostLossless.setMass_biUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:05:06.144836+00:00
-- url     : https://prove2.me/submissions/07884741-e420-4c19-855b-09dcf58f715f

import Definitions.Def_Bridges_MinEntropy
import Definitions.Def_Bridges_AlmostLosslessCompression
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] {ι : Type*} [DecidableEq α] (μ : FinProbDist α)
    (s : Finset ι) (t : ι → Finset α) :
    setMass μ (s.biUnion t) ≤ ∑ i ∈ s, setMass μ (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [setMass]
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hu : setMass μ (t i ∪ s.biUnion t) ≤ setMass μ (t i) + setMass μ (s.biUnion t) := by
      unfold setMass
      have h := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := μ.mass)
      have h0 : 0 ≤ ∑ x ∈ t i ∩ s.biUnion t, μ.mass x :=
        Finset.sum_nonneg (fun x _ => μ.mass_nonneg x)
      linarith
    linarith
