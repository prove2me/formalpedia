-- Prove2me | solution 1 for mme_stothers_general_target_pruning_assembly
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:49:03.723839+00:00
-- url     : https://prove2.me/submissions/77bf7716-da9e-4ff9-a758-4cfb9c70a181

import Definitions.Def_mme_stothers_general_outer_profile
import Theorems.Thm_mme_tripartite_target_isolation_pruning
import Mathlib.Data.Finset.Prod

open MME
open MME.StothersFourth

set_option autoImplicit false

theorem solution
    (base : Fin 10 → ℕ) (m : ℕ) (E : Finset (GenMarginalSupportedAddress base m))
    (hclosed : GenMarginalVertexClosed E) :
    ∃ G : Finset (GenExactOuterAddress base m),
      GenInducedModeDisjoint G ∧
      ((genExactTargetEdges E).card : ℝ) ≤
        (G.card : ℝ) + (genTargetAmbientCollisions E).card := by
  classical
  let T := genExactTargetEdges E
  let v : ∀ s : Fin 3,
      GenMarginalSupportedAddress base m →
        (Fin (genOuterLength base m) → Fin 9) :=
    fun s e ↦ e.1 s
  have hTE : T ⊆ E := by
    intro e he
    exact (Finset.mem_filter.mp
      (show e ∈ genExactTargetEdges E from he)).1
  obtain ⟨F, hFT, hdisjoint, hinduced, hcard⟩ :=
    mme_tripartite_target_isolation_pruning v E T hTE
  let liftExact : ↑F → GenExactOuterAddress base m := fun e ↦
    ⟨e.1.1, (Finset.mem_filter.mp
      (show e.1 ∈ genExactTargetEdges E from hFT e.2)).2⟩
  have hlift_injective : Function.Injective liftExact := by
    intro x y hxy
    have hbase : (liftExact x).1 = (liftExact y).1 :=
      congrArg (fun q : GenExactOuterAddress base m ↦ q.1) hxy
    exact Subtype.ext (Subtype.ext hbase)
  let G : Finset (GenExactOuterAddress base m) := F.attach.image liftExact
  have hcardG : G.card = F.card := by
    calc
      G.card = F.attach.card := by
        exact Finset.card_image_of_injective F.attach hlift_injective
      _ = F.card := Finset.card_attach
  refine ⟨G, ?_, ?_⟩
  · constructor
    · intro x y hxy s hsame
      obtain ⟨ux, _, hux⟩ := Finset.mem_image.mp x.2
      obtain ⟨uy, _, huy⟩ := Finset.mem_image.mp y.2
      have hraw_ne : ux.1 ≠ uy.1 := by
        intro h
        apply hxy
        apply Subtype.ext
        exact hux.symm.trans
          ((congrArg liftExact (Subtype.ext h)).trans huy)
      apply hdisjoint ux.1 ux.2 uy.1 uy.2 hraw_ne s
      have hxbase : ux.1.1 = x.1.1 := congrArg Subtype.val hux
      have hybase : uy.1.1 = y.1.1 := congrArg Subtype.val huy
      change ux.1.1 s = uy.1.1 s
      rw [hxbase, hybase]
      exact hsame
    · intro x y z hsupported
      obtain ⟨ux, _, hux⟩ := Finset.mem_image.mp x.2
      obtain ⟨uy, _, huy⟩ := Finset.mem_image.mp y.2
      obtain ⟨uz, _, huz⟩ := Finset.mem_image.mp z.2
      have hxbase : ux.1.1 = x.1.1 := congrArg Subtype.val hux
      have hybase : uy.1.1 = y.1.1 := congrArg Subtype.val huy
      have hzbase : uz.1.1 = z.1.1 := congrArg Subtype.val huz
      have hmixed :
          genMixedAddress ux.1.1 uy.1.1 uz.1.1 =
            genMixedAddress x.1.1 y.1.1 z.1.1 := by
        rw [hxbase, hybase, hzbase]
      have hsupportedRaw : GenCoordinatewiseSupported
          (genMixedAddress ux.1.1 uy.1.1 uz.1.1) := by
        rw [hmixed]
        exact hsupported
      obtain ⟨e, heE, hebase⟩ :=
        hclosed ux.1 (hTE (hFT ux.2))
          uy.1 (hTE (hFT uy.2)) uz.1 (hTE (hFT uz.2)) hsupportedRaw
      have heF : e ∈ F := by
        apply hinduced e heE
        intro s
        fin_cases s
        · refine ⟨ux.1, ux.2, ?_⟩
          simp [v, hebase, genMixedAddress]
        · refine ⟨uy.1, uy.2, ?_⟩
          simp [v, hebase, genMixedAddress]
        · refine ⟨uz.1, uz.2, ?_⟩
          simp [v, hebase, genMixedAddress]
      have heq_x : e = ux.1 := by
        by_contra hne
        apply hdisjoint e heF ux.1 ux.2 hne (0 : Fin 3)
        simp [v, hebase, genMixedAddress]
      have heq_y : e = uy.1 := by
        by_contra hne
        apply hdisjoint e heF uy.1 uy.2 hne (1 : Fin 3)
        simp [v, hebase, genMixedAddress]
      have heq_z : e = uz.1 := by
        by_contra hne
        apply hdisjoint e heF uz.1 uz.2 hne (2 : Fin 3)
        simp [v, hebase, genMixedAddress]
      have hxyExact : x.1 = y.1 := by
        exact hux.symm.trans
          ((congrArg liftExact
            (Subtype.ext (heq_x.symm.trans heq_y))).trans huy)
      have hyzExact : y.1 = z.1 := by
        exact huy.symm.trans
          ((congrArg liftExact
            (Subtype.ext (heq_y.symm.trans heq_z))).trans huz)
      exact ⟨Subtype.ext hxyExact, Subtype.ext hyzExact⟩
  · have hcardReal : (T.card : ℝ) ≤
        (F.card : ℝ) +
          (((T ×ˢ E).filter (fun p ↦
            p.1 ≠ p.2 ∧ ∃ s : Fin 3, v s p.1 = v s p.2)).card : ℝ) := by
      exact_mod_cast hcard
    simpa only [T, v, genTargetAmbientCollisions, hcardG] using hcardReal

