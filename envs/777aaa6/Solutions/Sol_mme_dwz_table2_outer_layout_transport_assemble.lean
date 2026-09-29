-- Prove2me | solution 1 for mme_dwz_table2_outer_layout_transport_assemble
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T14:31:06.48813+00:00
-- url     : https://prove2.me/submissions/dd4001e0-d033-4a70-b529-9dbec119cc8d

import Theorems.Thm_mme_dwz_table2_split_assignments_embed_typical_fiber

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZTable2OuterLayoutTransport

private abbrev TaggedPosition (m : ℕ) :=
  Σ r : MME.DWZTable2Cardinality.SplitRegion,
    MME.DWZTable2Cardinality.RegionPosition m r

private abbrev TypicalFiber
    (m : ℕ) {Position : Type*}
    [Fintype Position]
    (K : Position → Fin 5) :=
  {small : Position → Fin 3 × Fin 3 //
    (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
    ∀ p, Fintype.card {t : Position // small t = p} =
      MME.DWZTable2Counts.gamma p * m}

private abbrev CanonicalTypicalFiber (m : ℕ) :=
  {small : TaggedPosition m → Fin 3 × Fin 3 //
    (∀ x, MME.DWZTable2Counts.coarseOf (small x) =
      MME.DWZTable2Cardinality.coarseDegree x.1) ∧
    ∀ p, Fintype.card {x : TaggedPosition m // small x = p} =
      MME.DWZTable2Counts.gamma p * m}

/-- Reindex one canonical typical word along a literal regional layout. -/
private def transportTypical
    (m : ℕ) {Position : Type*}
    [Fintype Position]
    (K : Position → Fin 5)
    (layout : TaggedPosition m ≃ Position)
    (hlayout : ∀ x, K (layout x) =
      MME.DWZTable2Cardinality.coarseDegree x.1)
    (small : CanonicalTypicalFiber m) : TypicalFiber m K := by
  refine ⟨fun t ↦ small.1 (layout.symm t), ?_, ?_⟩
  · intro t
    calc
      MME.DWZTable2Counts.coarseOf (small.1 (layout.symm t)) =
          MME.DWZTable2Cardinality.coarseDegree (layout.symm t).1 :=
        small.2.1 (layout.symm t)
      _ = K (layout (layout.symm t)) := (hlayout (layout.symm t)).symm
      _ = K t := by rw [layout.apply_symm_apply]
  · intro p
    let fiberEquiv :
        {x : TaggedPosition m // small.1 x = p} ≃
          {t : Position // small.1 (layout.symm t) = p} :=
      Equiv.subtypeEquiv layout (fun x ↦ by simp)
    rw [← Fintype.card_congr fiberEquiv]
    exact small.2.2 p

private theorem transportTypical_injective
    (m : ℕ) {Position : Type*}
    [Fintype Position]
    (K : Position → Fin 5)
    (layout : TaggedPosition m ≃ Position)
    (hlayout : ∀ x, K (layout x) =
      MME.DWZTable2Cardinality.coarseDegree x.1) :
    Function.Injective (transportTypical m K layout hlayout) := by
  intro small₁ small₂ h
  apply Subtype.ext
  funext x
  have hx := congrArg
    (fun small : TypicalFiber m K ↦ small.1 (layout x)) h
  simpa [transportTypical] using hx

end MME.DWZTable2OuterLayoutTransport

open MME.DWZTable2OuterLayoutTransport

theorem solution
    (m : ℕ)
    {Outer Position : Type*}
    [Finite Outer] [Fintype Position]
    (K : Position → Fin 5)
    (layout : ∀ _I : Outer,
      (Σ r : MME.DWZTable2Cardinality.SplitRegion,
        MME.DWZTable2Cardinality.RegionPosition m r) ≃ Position)
    (hlayout : ∀ (I : Outer) x,
      K (layout I x) = MME.DWZTable2Cardinality.coarseDegree x.1) :
    let BtypicalK :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    ∃ assemble :
        (Σ _I : Outer, MME.DWZTable2Cardinality.SplitAssignments m) →
          BtypicalK,
      ∀ I, Function.Injective (fun A ↦ assemble ⟨I, A⟩) := by
  classical
  dsimp only
  rcases mme_dwz_table2_split_assignments_embed_typical_fiber m with
    ⟨_hcoarse, encode, hencode⟩
  let assemble :
      (Σ _I : Outer, MME.DWZTable2Cardinality.SplitAssignments m) →
        TypicalFiber m K :=
    fun z ↦ transportTypical m K (layout z.1) (hlayout z.1) (encode z.2)
  refine ⟨assemble, ?_⟩
  intro I A B hAB
  apply hencode
  apply transportTypical_injective m K (layout I) (hlayout I)
  exact hAB
