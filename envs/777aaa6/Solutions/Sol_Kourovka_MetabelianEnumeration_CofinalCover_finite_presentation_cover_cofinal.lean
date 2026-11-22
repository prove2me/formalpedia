-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.finite_presentation_cover_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:31:54.749123+00:00
-- url     : https://prove2.me/submissions/630eff04-f2bb-4170-8c3d-ac22075831f4

import Definitions.Def_Kourovka_Cofinality_CofinalRealization
import Definitions.Def_Kourovka_Halfspaces_BieriStrebelNecessity
import Definitions.Def_Kourovka_Cofinality_Cofinality
import Theorems.Thm_Kourovka_MetabelianEnumeration_BieriStrebelNecessity_tame_of_finite_presentation
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelianQuotientMap_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelian_pullback_finitely_presented_on_fin
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_exists_tame_cover_data
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_first_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_lattice_kernel_finite_module


set_option autoImplicit true
noncomputable section
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule ValuationModule SignedTameness
open TamenessCompactness
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution {k : ℕ} (R : List (FreeGroup (Fin k)))
    (hG : Metabelian (PresentedGroup (CentralExtension.relSet R))) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ data : Datum k a,
      ConeVerifier.ConeCover (data.polynomials.map polynomialSupport) ∧
      ∀ radius : ℕ, ∃ f : FiniteCover.GroupOf data radius →*
        PresentedGroup (CentralExtension.relSet R), Function.Surjective f := by
  classical
  -- Replace the abelian quotient by a free abelian lattice via a central pullback.
  let π := latticeProjection R
  have hπ : Function.Surjective π := latticeProjection_surjective R
  letI := lattice_kernel_commutative R hG
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
  -- Finite normal generation gives a finitely generated Laurent module.
  have hf : Module.Finite (GroupRing (Lattice k)) (Additive π.ker) :=
    lattice_kernel_finite_module R hG
  obtain ⟨n, S, ⟨e⟩⟩ := abelian_pullback_finitely_presented_on_fin R
  -- Finite presentation forces the directional finiteness used by Bieri-Strebel.
  have ht : Tame (k := k) (Additive π.ker) :=
    BieriStrebelNecessity.tame_of_finite_presentation (CentralExtension.relSet S)
      (List.finite_toSet S) e π hπ hf
  -- Extract finitely many Laurent relations whose supports cover all directions.
  obtain ⟨a, ha, data, hcone, hmaps⟩ := exists_tame_cover_data π hπ hf ht
  refine ⟨a, ha, data, hcone, ?_⟩
  intro radius
  obtain ⟨f, hsurj⟩ := hmaps radius
  -- Compose with the pullback projection to recover the original group.
  exact ⟨(first Abelianization.of (abelianQuotientMap R)).comp f,
    (first_surjective _ _ (abelianQuotientMap_surjective R)).comp hsurj⟩
end Kourovka.MetabelianEnumeration.CofinalCover
