-- Prove2me | solution 1 for SimpleGraph.IsStarSum.chromaticNumber_eq_cliqueNum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T06:13:25.898761+00:00
-- url     : https://prove2.me/submissions/b922de35-89a8-43e9-b1ad-ab560f280b7c

import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam

open SimpleGraph

open SimpleGraph in
/-- **If every part has `χ = ω`, so does the star sum.** -/
theorem solution {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
    (h : IsStarSum G H A v) [Fintype V] [Fintype ι] [Nonempty ι]
    (hpart : ∀ i, (H i).chromaticNumber = ((H i).cliqueNum : ℕ∞)) :
    G.chromaticNumber = (G.cliqueNum : ℕ∞) := by
  classical
  have hsup : G.chromaticNumber = Finset.univ.sup (fun i => (H i).chromaticNumber) := by
    classical
    have glue : ∀ {k : ℕ}, (∀ i, (H i).Colorable k) → G.Colorable k := by
      intro k hk
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
    have hle : ∀ i, H i ≤ G := fun i => by rw [h.sup_eq]; exact le_iSup H i
    have fin : ∀ K : SimpleGraph V, K.chromaticNumber ≠ ⊤ := fun K =>
      ne_top_of_le_ne_top (ENat.coe_ne_top _) (K.colorable_of_fintype).chromaticNumber_le
    apply le_antisymm
    · obtain ⟨i1, -, hi1⟩ :=
        Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => (H i).chromaticNumber)
      have hcol : ∀ i, (H i).Colorable (H i1).chromaticNumber.toNat := by
        intro i
        have h1 : (H i).chromaticNumber ≤ (H i1).chromaticNumber := by
          have hl := Finset.le_sup (f := fun i => (H i).chromaticNumber) (Finset.mem_univ i)
          rwa [hi1] at hl
        refine (H i).colorable_chromaticNumber_of_fintype.mono ?_
        exact ENat.toNat_le_toNat h1 (fin _)
      calc G.chromaticNumber ≤ ((H i1).chromaticNumber.toNat : ℕ∞) := (glue hcol).chromaticNumber_le
        _ = (H i1).chromaticNumber := ENat.coe_toNat (fin _)
        _ = _ := hi1.symm
    · exact Finset.sup_le (fun i _ => SimpleGraph.chromaticNumber_mono G (hle i))
  have hle : ∀ i, H i ≤ G := fun i => by rw [h.sup_eq]; exact le_iSup H i
  have hω : ∀ i, (H i).cliqueNum ≤ G.cliqueNum := by
    intro i
    obtain ⟨s, hs⟩ := (H i).exists_isNClique_cliqueNum
    rw [← hs.card_eq]
    exact SimpleGraph.IsClique.card_le_cliqueNum (tc := hs.isClique.mono (hle i))
  apply le_antisymm
  · rw [hsup]
    apply Finset.sup_le
    intro i _
    rw [hpart i]
    exact_mod_cast hω i
  · exact SimpleGraph.cliqueNum_le_chromaticNumber
