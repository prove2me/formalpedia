-- Prove2me | solution 1 for Heisenberg125.Heis.productOneFree_anomalySeq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T20:19:14.052099+00:00
-- url     : https://prove2.me/submissions/843c812e-9cfe-49ae-8427-aec4a02084b5

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_PrimeTwoAnomaly

open Heisenberg125 Heisenberg125.Heis in
theorem solution : ProductOneFree anomalySeq := by
  have hseq : anomalySeq = [⟨0, 1, 0⟩, ⟨1, 1, 0⟩, ⟨1, 1, 0⟩, ⟨1, 1, 0⟩] := rfl
  -- the first two coordinates of a product are the coordinate sums
  have hab : ∀ L : List (Heis 2),
      L.prod.a = (L.map Heis.a).sum ∧ L.prod.b = (L.map Heis.b).sum := by
    intro L
    induction L with
    | nil => exact ⟨rfl, rfl⟩
    | cons g L ih =>
      simp only [List.prod_cons, List.map_cons, List.sum_cons, mul_a, mul_b, ih.1, ih.2]
      exact ⟨trivial, trivial⟩
  -- only the sub-multiset {xy, xy} has trivial abelian image
  have hsub : ∀ T ∈ anomalySeq.sublists, T ≠ [] → (T.map Heis.a).sum = 0 →
      (T.map Heis.b).sum = 0 → T = List.replicate 2 (⟨1, 1, 0⟩ : Heis 2) := by
    rw [hseq]
    decide
  intro T hT hne ⟨M, hM, hprod⟩
  have h1 := hab M
  rw [hprod] at h1
  have ha : (T.map Heis.a).sum = 0 := by
    rw [← (hM.map Heis.a).sum_eq, ← h1.1]
    rfl
  have hb : (T.map Heis.b).sum = 0 := by
    rw [← (hM.map Heis.b).sum_eq, ← h1.2]
    rfl
  have hT2 := hsub T (List.mem_sublists.2 hT) hne ha hb
  rw [hT2] at hM
  have hM2 := List.perm_replicate.1 hM
  rw [hM2] at hprod
  revert hprod
  decide
