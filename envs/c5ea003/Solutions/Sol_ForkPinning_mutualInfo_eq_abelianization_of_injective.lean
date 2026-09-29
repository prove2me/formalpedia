-- Prove2me | solution 1 for ForkPinning.mutualInfo_eq_abelianization_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:26:26.204004+00:00
-- url     : https://prove2.me/submissions/e90ff3c2-3e39-4431-a548-e9335ad6b304

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningDataProcessing
import Definitions.Def_Probability_ForkPinningGalois
open ForkPinning Finset Real in
theorem solution {β : Type*} [Fintype β] [DecidableEq β] {G : Type*} [Group G] [Fintype G]
    [Nonempty G] {A : Type*} [CommGroup A] [Fintype A] [DecidableEq A]
    [Fintype (Abelianization G)] [DecidableEq (Abelianization G)]
    (f : G →* A) (Y : G → β) (hinj : Function.Injective (Abelianization.lift f)) :
    mutualInfo (fun g : G => f g) Y = mutualInfo (fun g : G => Abelianization.of g) Y := by
  have hfl : ∀ g : G, f g = Abelianization.lift f (Abelianization.of g) := by
    intro g
    simp
  -- the marginal entropies agree: an injective relabelling preserves fibres
  have hfib1 : ∀ z : Abelianization G,
      fiber (fun g : G => f g) (Abelianization.lift f z)
        = fiber (fun g : G => Abelianization.of g) z := by
    intro z
    ext g
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hg
      apply hinj
      rw [← hfl g]
      exact hg
    · intro hg
      rw [hfl g, hg]
  have hzero1 : ∀ a ∈ (Finset.univ : Finset A),
      a ∉ Finset.image (fun z : Abelianization G => Abelianization.lift f z) Finset.univ →
      negMulLog (prb (fun g : G => f g) a) = 0 := by
    intro a _ ha
    have hemp : fiber (fun g : G => f g) a = ∅ := by
      ext g
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro hg
      exact ha (Finset.mem_image.mpr ⟨Abelianization.of g, Finset.mem_univ _,
        by rw [← hfl g]; exact hg⟩)
    have : prb (fun g : G => f g) a = 0 := by
      simp only [prb, hemp, Finset.card_empty, Nat.cast_zero, zero_div]
    rw [this]
    simp
  have hHeq : H (fun g : G => f g) = H (fun g : G => Abelianization.of g) := by
    simp only [H]
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero1,
      Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    simp only [prb, hfib1]
  -- the joint entropies agree for the same reason
  have hfib2 : ∀ (z : Abelianization G) (b : β),
      fiber (joint (fun g : G => f g) Y) (Abelianization.lift f z, b)
        = fiber (joint (fun g : G => Abelianization.of g) Y) (z, b) := by
    intro z b
    ext g
    simp only [fiber, joint, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · intro hg
      refine ⟨hinj ?_, hg.2⟩
      rw [← hfl g]
      exact hg.1
    · intro hg
      exact ⟨by rw [hfl g, hg.1], hg.2⟩
  have hzero2 : ∀ p ∈ (Finset.univ : Finset (A × β)),
      p ∉ Finset.image (fun q : Abelianization G × β => (Abelianization.lift f q.1, q.2))
        Finset.univ →
      negMulLog (prb (joint (fun g : G => f g) Y) p) = 0 := by
    intro p _ hp
    have hemp : fiber (joint (fun g : G => f g) Y) p = ∅ := by
      ext g
      simp only [fiber, joint, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro hg
      refine hp (Finset.mem_image.mpr ⟨(Abelianization.of g, Y g), Finset.mem_univ _, ?_⟩)
      rw [← hfl g]
      exact hg
    have : prb (joint (fun g : G => f g) Y) p = 0 := by
      simp only [prb, hemp, Finset.card_empty, Nat.cast_zero, zero_div]
    rw [this]
    simp
  have hHJeq : H (joint (fun g : G => f g) Y)
      = H (joint (fun g : G => Abelianization.of g) Y) := by
    simp only [H]
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero2,
      Finset.sum_image (fun x _ y _ hxy => by
        have h := Prod.ext_iff.mp hxy
        exact Prod.ext_iff.mpr ⟨hinj h.1, h.2⟩)]
    simp only [prb, hfib2]
  simp only [mutualInfo, hHeq, hHJeq]
