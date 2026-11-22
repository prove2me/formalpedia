-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SchreierHeights.halfspace_generation_of_section
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:23:34.586242+00:00
-- url     : https://prove2.me/submissions/7d114c37-9054-4bdf-920f-fec641e60831

import Definitions.Def_Kourovka_Halfspaces_SchreierPaths
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeneration
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_transfer_generation
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_mono
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceSplitting_abelian_presentation_one_side_generates
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_augmented_relators_one_side
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_generatorWord_eval
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_generatorWord_path
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_representative_height
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_schreierKernelEquiv_of
import Theorems.Thm_Kourovka_MetabelianEnumeration_SchreierHeights_symbols_cover
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_presentationEquiv_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
attribute [local simp] Kourovka.MetabelianEnumeration.SchreierHeights.generatorWord_eval
attribute [local simp] Kourovka.MetabelianEnumeration.SchreierHeights.schreierKernelEquiv_of
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.presentationEquiv_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk



set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry HalfspaceSplitting HalfspaceLoops
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X L : Type} [AddCommGroup L] [DecidableEq X]
namespace Kourovka.MetabelianEnumeration.SchreierHeights
theorem _root_.solution (R : Set (FreeGroup X))
    (π : PresentedGroup R →* Multiplicative L) (χ : L →+ ℝ)
    (S : Transversal (preKernel R π))
    (D B μ : ℝ) (hD0 : 0 ≤ D) (hDB : D ≤ B) (hμ : 2 * B ≤ μ)
    (hD : ∀ x, |value (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R)))
      (FreeGroup.of x)| ≤ D)
    (hR : ∀ r ∈ R, (r.toWord.length : ℝ) * D ≤ B)
    (hsafe : ∀ t : S.vertices,
      PathIn (step (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))))
        (fun z => min 0 (value (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))) t.val) ≤ z ∧
          z ≤ max μ (value (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))) t.val))
        0 t.val.toWord)
    (habelian : ∀ a b : π.ker, Commute a b) :
    Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => 0 ≤ z)) = ⊤ ∨
      Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => z ≤ μ)) = ⊤ := by
  let π₀ := π.comp (PresentedGroup.mk R)
  let θ := χ.toMultiplicative.comp π₀
  let e := schreierKernelEquiv R π S
  have hh (w : FreeGroup X) : value θ (S.rep w) = value θ w :=
    representative_height π₀ χ.toMultiplicative S w
  have hab : ∀ a b : PresentedGroup (S.relators R),
      Commute a b := by
    intro a b
    apply (commute_map_iff e.injective).mp
    exact habelian (e a) (e b)
  have hsplit := abelian_presentation_one_side_generates
    (S.relators R)
    (symbolsIn θ S (fun z => 0 ≤ z)) (symbolsIn θ S (fun z => z ≤ μ))
    (symbols_cover π₀ χ.toMultiplicative S D μ hD (by linarith))
    (augmented_relators_one_side π₀ χ.toMultiplicative S R D B μ hD0 hDB hμ hD hR hsafe) hab
  have htransfer (P : ℝ → Prop)
      (hP : ∀ t : S.vertices, P (value θ t.val) →
        PathIn (step θ) P 0 t.val.toWord)
      (hgen : Subgroup.closure (PresentedGroup.of '' symbolsIn θ S P :
        Set (PresentedGroup (S.relators R))) = ⊤) :
      Subgroup.closure (loopSet π χ PresentedGroup.of P) = ⊤ := by
    apply transfer_generation e _ _ hgen
    rintro _ ⟨z, hz, rfl⟩
    have hz' : P (value θ z.1.val) ∧ P (value θ (z.1.val * FreeGroup.of z.2)) := hz
    refine ⟨generatorWord S z, ?_, ?_⟩
    · have heval (w : FreeGroup X) : FreeGroup.lift (PresentedGroup.of : X → PresentedGroup R) w =
          PresentedGroup.mk R w := (FreeGroup.lift_unique (PresentedGroup.mk R) (fun _ => rfl)).symm
      rw [heval, generatorWord_eval]
      exact (schreierKernelEquiv_of R π S z).symm
    · change PathIn (step θ) P 0 (generatorWord S z)
      apply generatorWord_path θ S hh P z hz (hP z.1 hz'.1)
      apply hP ⟨S.rep (z.1.val * FreeGroup.of z.2), ⟨_, rfl⟩⟩
      simpa only [hh] using hz'.2
  rcases hsplit with h | h
  · left
    apply htransfer (fun z => 0 ≤ z) _ h
    intro t ht
    apply (hsafe t).mono
    intro z hz
    have hzlo : min 0 (value θ t.val) ≤ z := hz.1
    simpa only [min_eq_left ht] using hzlo
  · right
    apply htransfer (fun z => z ≤ μ) _ h
    intro t ht
    apply (hsafe t).mono
    intro z hz
    have hzhi : z ≤ max μ (value θ t.val) := hz.2
    simpa only [max_eq_left ht] using hzhi
end Kourovka.MetabelianEnumeration.SchreierHeights
