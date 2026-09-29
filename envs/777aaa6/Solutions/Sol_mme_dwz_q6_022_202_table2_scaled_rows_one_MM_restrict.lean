-- Prove2me | solution 1 for mme_dwz_q6_022_202_table2_scaled_rows_one_MM_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:47:12.537741+00:00
-- url     : https://prove2.me/submissions/0fc6ff5b-7cd2-474f-a4e8-7bf0eb3f4afb

import Mathlib.Tactic
import Theorems.Thm_mme_dwz_q6_022_202_component_power_exact_basis_routers
import Theorems.Thm_mme_dwz_q6_row9_component_allowed_card_eq_restricted022
import Definitions.Def_mme_dwz_central_restricted_word_projectors
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes

open PiTensorProduct TensorProduct Module
open MME MME.DWZFineChannel MME.DWZComponentRestriction
open MME.DWZTable2Component022

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace MME.DWZCentral022InterfaceDescent

noncomputable def allowedEquivFin
    {ι : Type u} [Fintype ι] (allowed : ι → Prop) :
    {x : ι // allowed x} ≃ Fin (Nat.card {x : ι // allowed x}) := by
  classical
  letI : Fintype {x : ι // allowed x} := Fintype.ofFinite _
  exact (Fintype.equivFin _).trans
    (finCongr Nat.card_eq_fintype_card.symm)

noncomputable def allowedCoordEmbedding
    {ι : Type u} [Fintype ι] {P : ℕ}
    (allowed : ι → Prop) (coord : ι ↪ Fin P) :
    Fin (Nat.card {x : ι // allowed x}) ↪ Fin P where
  toFun i := coord ((allowedEquivFin allowed).symm i).1
  inj' := by
    intro i j h
    apply (allowedEquivFin allowed).symm.injective
    apply Subtype.ext
    exact coord.injective h

theorem allowedCoordEmbedding_outside
    {ι : Type u} [Fintype ι] {P : ℕ}
    (allowed : ι → Prop) (coord : ι ↪ Fin P)
    (w : ι) (hw : ¬ allowed w) :
    ∀ i, allowedCoordEmbedding allowed coord i ≠ coord w := by
  intro i hi
  apply hw
  have hword : ((allowedEquivFin allowed).symm i).1 = w :=
    coord.injective hi
  exact hword ▸ ((allowedEquivFin allowed).symm i).2

private theorem funLeft_single_outside
    (K : Type u) [Field K] {A B : Type*}
    [DecidableEq A] (f : B → A) (a : A)
    (h : ∀ b, f b ≠ a) :
    LinearMap.funLeft K K f (Pi.single a 1) = (0 : B → K) := by
  funext b
  simp [LinearMap.funLeft_apply, h b]

theorem central022Projector_Z_outside
    {K : Type u} [Field K] {m D : ℕ}
    (e : Fin D ↪ Fin ((6 ^ 2 + 2) ^ m))
    (k' : Fin ((6 ^ 2 + 2) ^ m))
    (hout : ∀ k : Fin D, e k ≠ k') :
    central022RestrictedProjector (K := K) e 2
        (central022FlatMMVec K 6 m k' 2) = 0 := by
  change (LinearMap.funLeft K K
      (fun ab : Fin D × Fin 1 ↦ (e ab.1, unitWordIndex m)))
      (Pi.single (k', unitWordIndex m) 1) = 0
  apply funLeft_single_outside
  intro ab h
  exact hout ab.1 (congrArg Prod.fst h)

theorem central202Projector_Z_outside
    {K : Type u} [Field K] {m D : ℕ}
    (e : Fin D ↪ Fin ((6 ^ 2 + 2) ^ m))
    (k' : Fin ((6 ^ 2 + 2) ^ m))
    (hout : ∀ k : Fin D, e k ≠ k') :
    central202RestrictedProjector (K := K) e 2
        (central202FlatMMVec K 6 m k' 2) = 0 := by
  change (LinearMap.funLeft K K
      (fun ab : Fin 1 × Fin D ↦ (unitWordIndex m, e ab.2)))
      (Pi.single (unitWordIndex m, k') 1) = 0
  apply funLeft_single_outside
  intro ab h
  exact hout ab.2 (congrArg Prod.snd h)

end MME.DWZCentral022InterfaceDescent

open MME.DWZCentral022InterfaceDescent

theorem solution
    (K : Type u) [Field K] (m : ℕ) :
    let D := Nat.card (Restricted022Word 6
      (table2Power022 (10366945 * m))
      (table2OuterCount022 (10366945 * m))
      (table2MiddleCount022 (10366945 * m)))
    TensorObj.Restrict (MMObj K 1 1 D)
        (restrictedComponentPower K (9 : Fin 15) m) ∧
      TensorObj.Restrict (MMObj K D 1 1)
        (restrictedComponentPower K (10 : Fin 15) m) := by
  let I := PowIndex (LiftedCoarsePair.{u} 6 2)
    (MME.DWZTable2Counts.component 9 * m)
  let allowed9 : I → Prop := componentWordAllowed (9 : Fin 15) m
  let D9 := Nat.card {w : I // allowed9 w}
  obtain ⟨⟨coord9, router9, hrouter9, hbasis9⟩,
      ⟨coord10, router10, hrouter10, hbasis10⟩⟩ :=
    mme_dwz_q6_022_202_component_power_exact_basis_routers K m
  let e9 : Fin D9 ↪
      Fin ((6 ^ 2 + 2) ^ (MME.DWZTable2Counts.component 9 * m)) :=
    allowedCoordEmbedding allowed9 coord9
  let f9 : ∀ s : Fin 3,
      (((canonicalComponentBlock K (9 : Fin 15)).kronPow
        (MME.DWZTable2Counts.component 9 * m)).V s) →ₗ[K]
        (MMObj K 1 1 D9).V s := fun s ↦
    (central022RestrictedProjector (K := K) e9 s).comp (router9 s)
  have hmap9 : PiTensorProduct.map f9
      ((canonicalComponentBlock K (9 : Fin 15)).kronPow
        (MME.DWZTable2Counts.component 9 * m)).t =
      (MMObj K 1 1 D9).t := by
    change PiTensorProduct.map
        (fun s ↦ (central022RestrictedProjector (K := K) e9 s) ∘ₗ
          router9 s) _ = _
    rw [PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [hrouter9,
      central022RestrictedProjector_maps_tensor]
  letI : DecidablePred allowed9 := Classical.decPred _
  have hvanish9 : ∀ w, ¬ allowed9 w →
      f9 2 (componentPowerZBasis K (9 : Fin 15) m w) = 0 := by
    intro w hw
    simp only [f9, LinearMap.comp_apply]
    rw [hbasis9]
    exact central022Projector_Z_outside e9 (coord9 w)
      (allowedCoordEmbedding_outside allowed9 coord9 w hw)
  have hrestrict9 := mme_restrict_basisZAllowedSubtensor_of_vanishes
    ((canonicalComponentBlock K (9 : Fin 15)).kronPow
      (MME.DWZTable2Counts.component 9 * m))
    (MMObj K 1 1 D9)
    (componentPowerZBasis K (9 : Fin 15) m) allowed9 f9 hmap9 hvanish9
  have hrow9 : TensorObj.Restrict (MMObj K 1 1 D9)
      (restrictedComponentPower K (9 : Fin 15) m) := by
    simpa only [restrictedComponentPower, componentPowerProjectionGrading,
      allowed9] using hrestrict9

  let I10 := PowIndex (LiftedCoarsePair.{u} 6 2)
    (MME.DWZTable2Counts.component 10 * m)
  let allowed10 : I10 → Prop := componentWordAllowed (10 : Fin 15) m
  let D10 := Nat.card {w : I10 // allowed10 w}
  let e10 : Fin D10 ↪
      Fin ((6 ^ 2 + 2) ^ (MME.DWZTable2Counts.component 10 * m)) :=
    allowedCoordEmbedding allowed10 coord10
  let f10 : ∀ s : Fin 3,
      (((canonicalComponentBlock K (10 : Fin 15)).kronPow
        (MME.DWZTable2Counts.component 10 * m)).V s) →ₗ[K]
        (MMObj K D10 1 1).V s := fun s ↦
    (central202RestrictedProjector (K := K) e10 s).comp (router10 s)
  have hmap10 : PiTensorProduct.map f10
      ((canonicalComponentBlock K (10 : Fin 15)).kronPow
        (MME.DWZTable2Counts.component 10 * m)).t =
      (MMObj K D10 1 1).t := by
    change PiTensorProduct.map
        (fun s ↦ (central202RestrictedProjector (K := K) e10 s) ∘ₗ
          router10 s) _ = _
    rw [PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [hrouter10,
      central202RestrictedProjector_maps_tensor]
  letI : DecidablePred allowed10 := Classical.decPred _
  have hvanish10 : ∀ w, ¬ allowed10 w →
      f10 2 (componentPowerZBasis K (10 : Fin 15) m w) = 0 := by
    intro w hw
    simp only [f10, LinearMap.comp_apply]
    rw [hbasis10]
    exact central202Projector_Z_outside e10 (coord10 w)
      (allowedCoordEmbedding_outside allowed10 coord10 w hw)
  have hrestrict10 := mme_restrict_basisZAllowedSubtensor_of_vanishes
    ((canonicalComponentBlock K (10 : Fin 15)).kronPow
      (MME.DWZTable2Counts.component 10 * m))
    (MMObj K D10 1 1)
    (componentPowerZBasis K (10 : Fin 15) m) allowed10 f10 hmap10 hvanish10
  have hrow10 : TensorObj.Restrict (MMObj K D10 1 1)
      (restrictedComponentPower K (10 : Fin 15) m) := by
    simpa only [restrictedComponentPower, componentPowerProjectionGrading,
      allowed10] using hrestrict10

  have hcard9 : D9 = Nat.card (Restricted022Word 6
      (table2Power022 (10366945 * m))
      (table2OuterCount022 (10366945 * m))
      (table2MiddleCount022 (10366945 * m))) := by
    simpa only [D9, I, allowed9] using
      mme_dwz_q6_row9_component_allowed_card_eq_restricted022.{u} m
  have hcard10 : D10 = D9 := by
    have hcomponent :
        MME.DWZTable2Counts.component (10 : Fin 15) =
          MME.DWZTable2Counts.component (9 : Fin 15) := by
      decide
    have hsplit :
        MME.DWZTable2Counts.split (10 : Fin 15) =
          MME.DWZTable2Counts.split (9 : Fin 15) := by
      decide
    simp only [D10, D9, I10, I, allowed10, allowed9,
      componentWordAllowed, MME.DWZSquare.shapeZ]
    rw [hcomponent, hsplit]
    rfl
  dsimp only
  constructor
  · simpa only [hcard9] using hrow9
  · simpa only [hcard10, hcard9] using hrow10
