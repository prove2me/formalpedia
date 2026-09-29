-- Prove2me | solution 1 for mme_dwz_table2_broken_copy_transport_to_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:15:11.95843+00:00
-- url     : https://prove2.me/submissions/6b2000ab-3544-4971-a0e3-9115466880c1

import Definitions.Def_mme_dwz_table2_useful_block
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Definitions.Def_mme_dwz_standard_labelled_z_blocks

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

namespace DWZBrokenCopyTransportSolution

noncomputable def reindexUsefulBlock
    (m : ℕ) {P Q : Type u} [Fintype P] [Fintype Q]
    (e : P ≃ Q) (outerQ : Q → Fin 15) (outerP : P → Fin 15)
    (houter : ∀ p, outerQ (e p) = outerP p)
    (small : MME.DWZTable2StandardForm.UsefulBlock m outerQ) :
    MME.DWZTable2StandardForm.UsefulBlock m outerP := by
  refine ⟨fun p ↦ small.1 (e p), ?_, ?_⟩
  · intro p
    exact (small.2.1 (e p)).trans
      (congrArg MME.DWZSquare.shapeZ (houter p))
  · intro s a
    let fiberEquiv :
        {p : P // outerP p = s ∧ (small.1 (e p)).1 = a} ≃
          {q : Q // outerQ q = s ∧ (small.1 q).1 = a} :=
      { toFun := fun p ↦
          ⟨e p.1, ⟨(houter p.1).trans p.2.1, p.2.2⟩⟩
        invFun := fun q ↦
          ⟨e.symm q.1, ⟨by
            rw [← houter (e.symm q.1)]
            simpa using q.2.1, by simpa using q.2.2⟩⟩
        left_inv := fun p ↦ by apply Subtype.ext; simp
        right_inv := fun q ↦ by apply Subtype.ext; simp }
    exact (Fintype.card_congr fiberEquiv).trans (small.2.2 s a)

noncomputable def usefulBlockPositionEquiv
    (m : ℕ) {P Q : Type u} [Fintype P] [Fintype Q]
    (e : P ≃ Q) (outerQ : Q → Fin 15) (outerP : P → Fin 15)
    (houter : ∀ p, outerQ (e p) = outerP p) :
    MME.DWZTable2StandardForm.UsefulBlock m outerQ ≃
      MME.DWZTable2StandardForm.UsefulBlock m outerP := by
  let houterSymm : ∀ q, outerP (e.symm q) = outerQ q := by
    intro q
    simpa using (houter (e.symm q)).symm
  exact
    { toFun := reindexUsefulBlock m e outerQ outerP houter
      invFun := reindexUsefulBlock m e.symm outerP outerQ houterSymm
      left_inv := by
        intro small
        apply Subtype.ext
        funext q
        simp [reindexUsefulBlock]
      right_inv := by
        intro small
        apply Subtype.ext
        funext p
        simp [reindexUsefulBlock] }

noncomputable def groupedPositionEquiv
    {N m : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m) :
    MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N := by
  let fiberEquiv : ∀ s : Fin 15,
      Fin (MME.DWZTable2Counts.component s * m) ≃
        {r : Fin N // outer r = s} := fun s ↦
    Fintype.equivOfCardEq (by simpa using (houter s).symm)
  exact (Equiv.sigmaCongrRight fiberEquiv).trans
    (Equiv.sigmaFiberEquiv outer)

theorem groupedPositionEquiv_outer
    {N m : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (p : MME.DWZComponentRestriction.GroupedPosition m) :
    outer (groupedPositionEquiv outer houter p) =
      MME.DWZComponentRestriction.groupedOuter p := by
  rcases p with ⟨s, r⟩
  change outer
      (((Fintype.equivOfCardEq _ :
        Fin (MME.DWZTable2Counts.component s * m) ≃
          {r : Fin N // outer r = s}) r).1) = s
  exact ((Fintype.equivOfCardEq _ :
    Fin (MME.DWZTable2Counts.component s * m) ≃
      {r : Fin N // outer r = s}) r).2

end DWZBrokenCopyTransportSolution

theorem solution
    {N m : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m outer)) :
    ∃ positionEquiv :
        MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N,
      (∀ p, outer (positionEquiv p) =
        MME.DWZComponentRestriction.groupedOuter p) ∧
      ∃ blockEquiv :
          MME.DWZTable2StandardForm.UsefulBlock m outer ≃
            MME.DWZComponentRestriction.DWZStandardBlock m,
        (∀ small p,
          (blockEquiv small).1 p = small.1 (positionEquiv p)) ∧
        ∃ transported : MME.DWZSquare.BrokenBlockCopy
            (MME.DWZComponentRestriction.DWZStandardBlock m),
          transported.nonholes.card = copy.nonholes.card ∧
          ∀ small,
            blockEquiv small ∈ transported.nonholes ↔
              small ∈ copy.nonholes := by
  classical
  let positionEquiv :=
    DWZBrokenCopyTransportSolution.groupedPositionEquiv outer houter
  have hposition : ∀ p, outer (positionEquiv p) =
      MME.DWZComponentRestriction.groupedOuter p :=
    DWZBrokenCopyTransportSolution.groupedPositionEquiv_outer outer houter
  let blockEquiv :=
    DWZBrokenCopyTransportSolution.usefulBlockPositionEquiv m
      positionEquiv outer
      (MME.DWZComponentRestriction.groupedOuter (m := m)) hposition
  let transported : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZComponentRestriction.DWZStandardBlock m) :=
    ⟨copy.nonholes.map blockEquiv.toEmbedding⟩
  refine ⟨positionEquiv, hposition, blockEquiv, ?_, transported, ?_, ?_⟩
  · intro small p
    rfl
  · simp [transported]
  · intro small
    simp [transported]
