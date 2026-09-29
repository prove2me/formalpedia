-- Prove2me | solution 1 for mme_dwz_source_raw_component_words_allowed_iff_useful
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:15:50.834629+00:00
-- url     : https://prove2.me/submissions/018deadb-debd-4413-805c-de7dfe0ac090

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Definitions.Def_mme_kron_pow_word_reindex

open MME

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

namespace MME.DWZSourceAligned

private theorem liftedCoarsePair_leftGrade_cast
    {c d : Fin 5} (h : c = d)
    (x : DWZComponentRestriction.LiftedCoarsePair.{u} 6 c) :
    (h ▸ x).leftGrade = x.leftGrade := by
  cases h
  rfl

/-- Exact letterwise transport along an outer-preserving grouped-position
equivalence identifies the fifteen component availability predicates with
the source-order useful-word predicate. -/
theorem rawComponentWordsAllowed_iff_addressWordUseful
    {N m : ℕ} {outer : Fin N → Fin 15}
    (e : DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      DWZComponentRestriction.groupedOuter p)
    (W : AddressZWord.{u} outer)
    (raw : ∀ s : Fin 15,
      DWZComponentRestriction.PowIndex
        (DWZComponentRestriction.LiftedCoarsePair.{u} 6
          (DWZSquare.shapeZ s))
        (DWZTable2Counts.component s * m))
    (hraw : ∀ p : DWZComponentRestriction.GroupedPosition m,
      HEq (DWZComponentRestriction.PowIndex.get
          (DWZTable2Counts.component p.1 * m) (raw p.1) p.2)
        (W (e p))) :
    (∀ s, DWZComponentRestriction.componentWordAllowed s m (raw s)) ↔
      addressWordUseful m outer W := by
  classical
  have rawLeftGrade : ∀ p : DWZComponentRestriction.GroupedPosition m,
      (DWZComponentRestriction.PowIndex.get
        (DWZTable2Counts.component p.1 * m) (raw p.1) p.2).leftGrade =
        (W (e p)).leftGrade := by
    intro p
    have hshape : DWZSquare.shapeZ (outer (e p)) =
        DWZSquare.shapeZ p.1 := congrArg DWZSquare.shapeZ (he p)
    have hcast : HEq (hshape ▸ W (e p)) (W (e p)) :=
      eqRec_heq hshape (W (e p))
    have hletter :
        DWZComponentRestriction.PowIndex.get
            (DWZTable2Counts.component p.1 * m) (raw p.1) p.2 =
          hshape ▸ W (e p) :=
      eq_of_heq ((hraw p).trans hcast.symm)
    rw [hletter]
    exact liftedCoarsePair_leftGrade_cast hshape (W (e p))
  let gradeFiberEquiv : ∀ (s : Fin 15) (a : Fin 3),
      {r : Fin (DWZTable2Counts.component s * m) //
        (DWZComponentRestriction.PowIndex.get
          (DWZTable2Counts.component s * m) (raw s) r).leftGrade = a} ≃
      {q : Fin N // outer q = s ∧ (W q).leftGrade = a} := by
    intro s a
    let F :
        {r : Fin (DWZTable2Counts.component s * m) //
          (DWZComponentRestriction.PowIndex.get
            (DWZTable2Counts.component s * m) (raw s) r).leftGrade = a} →
        {q : Fin N // outer q = s ∧ (W q).leftGrade = a} := fun r ↦ by
      refine ⟨e ⟨s, r.1⟩, ?_, ?_⟩
      · simpa only [DWZComponentRestriction.groupedOuter] using he ⟨s, r.1⟩
      · exact (rawLeftGrade ⟨s, r.1⟩).symm.trans r.2
    apply Equiv.ofBijective F
    constructor
    · intro r r' h
      apply Subtype.ext
      have heq : e ⟨s, r.1⟩ = e ⟨s, r'.1⟩ :=
        congrArg Subtype.val h
      have hp : (⟨s, r.1⟩ : DWZComponentRestriction.GroupedPosition m) =
          ⟨s, r'.1⟩ := e.injective heq
      apply Fin.ext
      exact congrArg (fun p : DWZComponentRestriction.GroupedPosition m ↦
        p.2.val) hp
    · rintro ⟨q, hqs, hqa⟩
      let p : DWZComponentRestriction.GroupedPosition m := e.symm q
      have hep : e p = q := e.apply_symm_apply q
      have hop : outer q = p.1 := by
        simpa only [p, DWZComponentRestriction.groupedOuter, hep] using he p
      have hps : p.1 = s := hop.symm.trans hqs
      rcases p with ⟨t, r⟩
      dsimp only at hps
      subst t
      have hep' : e ⟨s, r⟩ = q := by
        simpa only using hep
      have hgrade :
          (DWZComponentRestriction.PowIndex.get
            (DWZTable2Counts.component s * m) (raw s) r).leftGrade = a := by
        have hposGrade : (W (e ⟨s, r⟩)).leftGrade =
            (W q).leftGrade :=
          congrArg (fun x : Fin N ↦ (W x).leftGrade) hep'
        exact (rawLeftGrade ⟨s, r⟩).trans (hposGrade.trans hqa)
      refine ⟨⟨r, hgrade⟩, ?_⟩
      apply Subtype.ext
      exact hep'
  constructor
  · intro hall s a
    exact (Fintype.card_congr (gradeFiberEquiv s a)).symm.trans (hall s a)
  · intro hUseful s a
    exact (Fintype.card_congr (gradeFiberEquiv s a)).trans (hUseful s a)

end MME.DWZSourceAligned

theorem solution
    {N m : ℕ} {outer : Fin N → Fin 15}
    (e : MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      MME.DWZComponentRestriction.groupedOuter p)
    (W : MME.DWZSourceAligned.AddressZWord.{u} outer)
    (raw : ∀ s : Fin 15,
      MME.DWZComponentRestriction.PowIndex
        (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
          (MME.DWZSquare.shapeZ s))
        (MME.DWZTable2Counts.component s * m))
    (hraw : ∀ p : MME.DWZComponentRestriction.GroupedPosition m,
      HEq (MME.DWZComponentRestriction.PowIndex.get
          (MME.DWZTable2Counts.component p.1 * m) (raw p.1) p.2)
        (W (e p))) :
    (∀ s, MME.DWZComponentRestriction.componentWordAllowed s m (raw s)) ↔
      MME.DWZSourceAligned.addressWordUseful m outer W := by
  exact MME.DWZSourceAligned.rawComponentWordsAllowed_iff_addressWordUseful
    e he W raw hraw
