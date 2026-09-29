-- Prove2me | solution 1 for mme_CW_q6_paired_cyclic_color_pruning
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:43:12.529055+00:00
-- url     : https://prove2.me/submissions/5329a77c-2d37-49d6-8aa1-6b7006e80e8e

import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.Pigeonhole

open MME

/-- A coloring of the paired conflict graph yields a large retained set on
which every surviving paired triple is diagonal. This does not assert that
the retained set has uniform outer fibers. -/
theorem solution
    {N L G A H k : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (hk : 0 < k)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k)) :
    ∃ S : Finset (Fin A × Fin H),
      A * H / k ≤ S.card ∧
      ∀ p0 ∈ S, ∀ p1 ∈ S, ∀ p2 ∈ S,
        family.PairedCyclicSupported halving p0 p1 p2 →
          p0 = p1 ∧ p1 = p2 := by
  classical
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (f := coloring) (n := A * H / k) (by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (A * H) k)
  refine ⟨Finset.univ.filter (fun p => coloring p = c), hc, ?_⟩
  intro p0 hp0 p1 hp1 p2 hp2 hs
  have h0 : coloring p0 = c := (Finset.mem_filter.mp hp0).2
  have h1 : coloring p1 = c := (Finset.mem_filter.mp hp1).2
  have h2 : coloring p2 = c := (Finset.mem_filter.mp hp2).2
  by_contra hbad
  have eq_of_mem (p q : Fin A × Fin H)
      (hp : family.InPairedTriple p p0 p1 p2)
      (hq : family.InPairedTriple q p0 p1 p2)
      (heq : coloring p = coloring q) : p = q := by
    by_contra hne
    apply coloring.valid (show (family.pairedCyclicConflictGraph halving).Adj p q from ?_) heq
    exact ⟨hne, Or.inl ⟨p0, p1, p2, hs, hbad, hp, hq⟩⟩
  exact hbad ⟨eq_of_mem p0 p1 (Or.inl rfl) (Or.inr (Or.inl rfl)) (h0.trans h1.symm),
    eq_of_mem p1 p2 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (h1.trans h2.symm)⟩
