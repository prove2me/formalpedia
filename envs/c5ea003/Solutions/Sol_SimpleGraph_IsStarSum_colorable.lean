-- Prove2me | solution 1 for SimpleGraph.IsStarSum.colorable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T05:57:03.323105+00:00
-- url     : https://prove2.me/submissions/800887aa-b8b2-4e54-889b-c80377396a2a

import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam

open SimpleGraph

open SimpleGraph in
/-- **A star sum of `k`-colorable graphs is `k`-colorable**: glue the colorings after
permuting each so they agree at the centre. -/
theorem solution {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
    (h : IsStarSum G H A v) [Nonempty ι] {k : ℕ} (hk : ∀ i, (H i).Colorable k) :
    G.Colorable k := by
  classical
  have c : ∀ i, (H i).Coloring (Fin k) := fun i => (hk i).some
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  obtain ⟨σ, hσ⟩ : ∃ σ : ι → Equiv.Perm (Fin k), ∀ i, σ i (c i v) = c i0 v :=
    ⟨fun i => Equiv.swap (c i v) (c i0 v), fun i => Equiv.swap_apply_left _ _⟩
  have hcover : ∀ x, ∃ i, x ∈ A i := fun x => by
    have hx : x ∈ (⋃ i, A i) := by rw [h.union_eq]; trivial
    exact Set.mem_iUnion.mp hx
  obtain ⟨j, hj⟩ : ∃ j : V → ι, ∀ x, x ∈ A (j x) :=
    ⟨fun x => Classical.choose (hcover x), fun x => Classical.choose_spec (hcover x)⟩
  have hjk : ∀ x m, x ≠ v → x ∈ A m → j x = m := by
    intro x m hxv hxm
    by_contra hne
    have hm : x ∈ A (j x) ∩ A m := ⟨hj x, hxm⟩
    rw [h.inter_eq _ _ hne] at hm
    exact hxv hm
  refine ⟨Coloring.mk (fun x => if x = v then c i0 v else σ (j x) (c (j x) x)) ?_⟩
  intro x y hxy
  show (if x = v then c i0 v else σ (j x) (c (j x) x))
    ≠ (if y = v then c i0 v else σ (j y) (c (j y) y))
  rw [h.sup_eq, SimpleGraph.iSup_adj] at hxy
  obtain ⟨m, hm⟩ := hxy
  obtain ⟨hxA, hyA⟩ := h.support m hm
  have hne : x ≠ y := hm.ne
  by_cases hxv : x = v <;> by_cases hyv : y = v
  · exact absurd (hxv.trans hyv.symm) hne
  · rw [if_pos hxv, if_neg hyv, hjk y m hyv hyA, ← hσ m]
    intro e
    exact (c m).valid (hxv ▸ hm) ((σ m).injective e)
  · rw [if_neg hxv, if_pos hyv, hjk x m hxv hxA, ← hσ m]
    intro e
    exact (c m).valid (hyv ▸ hm) ((σ m).injective e)
  · rw [if_neg hxv, if_neg hyv, hjk x m hxv hxA, hjk y m hyv hyA]
    intro e
    exact (c m).valid hm ((σ m).injective e)
