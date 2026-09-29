-- Prove2me | solution 1 for mme_dwz_fourth_actual_blocks_profile_mask_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T09:08:07.29309+00:00
-- url     : https://prove2.me/submissions/414cab36-c3e5-424c-bf9e-d9c4bb139bd1

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Theorems.Thm_mme_CW_fourth_left_grade_fiber_nonempty_iff
import Theorems.Thm_mme_dwz_fine_block_masks_depend_only_on_coarse_and_profile_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex

open MME MME.StothersFourth MME.DWZSimultaneous MME.CompleteSplit
  MME.DWZRestrictedValue MME.DWZComponentRestriction BigOperators
open scoped Classical

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace MME.DWZFourthBlockBridge

abbrev Blocks {C : Type*} (p : C → IntegerZSplitProfile 5) (m : C → ℕ) :=
  (c : C) → {w : PowIndex (Fin 5) ((p c).length (m c)) //
    prescribedZWord id (p c) (m c) w}

abbrev Global {C : Type*} [DecidableEq C] {N : ℕ}
    (cell : Fin N → C) (p : C → IntegerZSplitProfile 5) (m : C → ℕ) :=
  {a : Fin N → Fin 5 // ∀ c z,
    Fintype.card {r : Fin N // cell r = c ∧ a r = z} = (p c).count z * m c}

theorem profile_equiv {C : Type*} [Fintype C] [DecidableEq C] {N : ℕ}
    (cell : Fin N → C) (p : C → IntegerZSplitProfile 5) (m : C → ℕ)
    (positions : Fin N ≃ Σ c, Fin ((p c).length (m c)))
    (hcell : ∀ c r, cell (positions.symm ⟨c, r⟩) = c) :
    ∃ E : Global cell p m ≃ Blocks p m,
      ∀ a c r, PowIndex.get _ (E a c).val r = a.val (positions.symm ⟨c, r⟩) := by
  classical
  let group : (Fin N → Fin 5) ≃ ((c : C) → Fin ((p c).length (m c)) → Fin 5) :=
    (Equiv.arrowCongr positions (Equiv.refl (Fin 5))).trans
      (Equiv.piCurry (fun (c : C) (_ : Fin ((p c).length (m c))) ↦ Fin 5))
  have hcard (a : Fin N → Fin 5) (c : C) (z : Fin 5) :
      Fintype.card {t : Fin N // cell t = c ∧ a t = z} =
        Fintype.card {r : Fin ((p c).length (m c)) // group a c r = z} := by
    let f : {r : Fin ((p c).length (m c)) // group a c r = z} →
        {t : Fin N // cell t = c ∧ a t = z} :=
      fun r ↦ ⟨positions.symm ⟨c, r.val⟩, hcell c r.val, r.property⟩
    symm
    apply Fintype.card_of_bijective (f := f)
    constructor
    · intro r s hrs
      apply Subtype.ext
      have hs : (⟨c, r.val⟩ : Σ c, Fin ((p c).length (m c))) = ⟨c, s.val⟩ :=
        positions.symm.injective (congrArg Subtype.val hrs)
      exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
    · intro t
      obtain ⟨⟨c', r⟩, hr⟩ := positions.symm.surjective t.val
      have hc : c' = c := (hcell c' r).symm.trans
        (by rw [hr]; exact t.property.1)
      subst c'
      refine ⟨⟨r, ?_⟩, ?_⟩
      · change a (positions.symm ⟨c,r⟩) = z
        simpa only [hr] using t.property.2
      · exact Subtype.ext hr
  let B (c : C) := {a : Fin ((p c).length (m c)) → Fin 5 //
    ∀ z, Fintype.card {r : Fin ((p c).length (m c)) // a r = z} =
      (p c).count z * m c}
  have hprop (a : Fin N → Fin 5) :
      (∀ c z, Fintype.card {r : Fin N // cell r = c ∧ a r = z} =
        (p c).count z * m c) ↔
      ∀ c z, Fintype.card {r : Fin ((p c).length (m c)) // group a c r = z} =
        (p c).count z * m c := by
    simp_rw [hcard]
  let middle : Global cell p m ≃ ((c : C) → B c) :=
    (group.subtypeEquiv hprop).trans (Equiv.subtypePiEquivPi
      (β := fun c : C ↦ Fin ((p c).length (m c)) → Fin 5)
      (p := fun c a ↦ ∀ z, Fintype.card {r : Fin ((p c).length (m c)) // a r = z} =
        (p c).count z * m c))
  let finish (c : C) : B c ≃
      {w : PowIndex (Fin 5) ((p c).length (m c)) // prescribedZWord id (p c) (m c) w} :=
    (PowIndex.equivFun (Fin 5) ((p c).length (m c))).symm.subtypeEquiv
      (fun a ↦ by simp [prescribedZWord, leftGradeCount, Fintype.card_subtype,
        PowIndex.equivFun])
  let ending : ((c : C) → B c) ≃ Blocks p m := Equiv.piCongrRight finish
  refine ⟨middle.trans ending, ?_⟩
  intro a c r
  change PowIndex.get _ (PowIndex.ofFun _ (group a.val c)) r = _
  rw [PowIndex.get_ofFun]
  rfl

theorem letter_supported {t : ℕ} (p : IntegerZSplitProfile t) (m : ℕ)
    (w : {w : PowIndex (Fin t) (p.length m) // prescribedZWord id p m w})
    (r : Fin (p.length m)) : 0 < p.count (PowIndex.get _ w.val r) := by
  classical
  have hpos : 0 < leftGradeCount id w.val (PowIndex.get _ w.val r) := by
    apply Finset.card_pos.mpr
    exact ⟨r, by simp⟩
  rw [w.property] at hpos
  exact Nat.pos_of_mul_pos_right hpos

theorem global_supported {C : Type*} [Fintype C] [DecidableEq C] {N : ℕ}
    (cell : Fin N → C) (p : C → IntegerZSplitProfile 5) (m : C → ℕ)
    (coarse : C → Fin 9)
    (hsupport : ∀ c a, 0 < (p c).count a →
      a.val ≤ (coarse c).val ∧ (coarse c).val ≤ a.val + 4)
    (a : Global cell p m) (r : Fin N) :
    (a.val r).val ≤ (coarse (cell r)).val ∧
      (coarse (cell r)).val ≤ (a.val r).val + 4 := by
  classical
  have hpos : 0 < Fintype.card {s : Fin N // cell s = cell r ∧ a.val s = a.val r} :=
    Fintype.card_pos_iff.mpr ⟨⟨r, rfl, rfl⟩⟩
  rw [a.property] at hpos
  exact hsupport _ _ (Nat.pos_of_mul_pos_right hpos)

theorem atomic_representative (q : ℕ) (hq : 0 < q) {N : ℕ}
    (coarse : Fin N → Fin 9) (a : Fin N → Fin 5)
    (ha : ∀ r, (a r).val ≤ (coarse r).val ∧ (coarse r).val ≤ (a r).val + 4) :
    ∃ w : WordIndex.{u} q 3 N,
      (∀ r, (∑ s, (label q 3 N w r s).val) = (coarse r).val) ∧
      ∀ r, fourthLeftTag (label q 3 N w r) = a r := by
  classical
  have hx (r : Fin N) :=
    (mme_CW_fourth_left_grade_fiber_nonempty_iff q hq (coarse r) (a r)).2 (ha r)
  choose x hxgrade hxleft using hx
  let flat : Fin N → Fin 4 → Fin (q + 2) := fun r s ↦
    ![(x r).1.1, (x r).1.2, (x r).2.1, (x r).2.2] s
  let w : WordIndex.{u} q 3 N := fun s ↦
    ULift.up (flat (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm s).2)
  have hw (r : Fin N) (s : Fin 4) :
      label q 3 N w r s = cwSquareCoordGrade q (flat r s) := by
    simp [label, w]
  refine ⟨w, ?_, ?_⟩
  · intro r
    simp only [hw]
    have hg := congrArg Fin.val (hxgrade r)
    change (cwSquareCoordGrade q (x r).1.1).val +
      ((cwSquareCoordGrade q (x r).1.2).val +
      ((cwSquareCoordGrade q (x r).2.1).val +
        (cwSquareCoordGrade q (x r).2.2).val)) = (coarse r).val
    change ((cwSquareCoordGrade q (x r).1.1).val +
      (cwSquareCoordGrade q (x r).1.2).val) +
      ((cwSquareCoordGrade q (x r).2.1).val +
        (cwSquareCoordGrade q (x r).2.2).val) = (coarse r).val at hg
    omega
  · intro r
    apply Fin.ext
    change (label q 3 N w r 0).val + (label q 3 N w r 1).val = (a r).val
    rw [hw, hw]
    exact congrArg Fin.val (hxleft r)

/-- Every product block is represented by an actual atomic CW coordinate word.
The equivalence counts grade blocks, not their generally unequal coordinate fibers. -/
theorem actual_block_representatives
    {C : Type*} [Fintype C] [DecidableEq C] {N : ℕ}
    (q : ℕ) (hq : 0 < q) (cell : Fin N → C)
    (p : C → IntegerZSplitProfile 5) (m : C → ℕ) (coarse : C → Fin 9)
    (positions : Fin N ≃ Σ c, Fin ((p c).length (m c)))
    (hcell : ∀ c r, cell (positions.symm ⟨c, r⟩) = c)
    (hsupport : ∀ c a, 0 < (p c).count a →
      a.val ≤ (coarse c).val ∧ (coarse c).val ≤ a.val + 4) :
    ∃ E : Global cell p m ≃ Blocks p m,
    ∃ rep : Blocks p m → WordIndex.{u} q 3 N,
      (∀ a c r, PowIndex.get _ (E a c).val r = a.val (positions.symm ⟨c, r⟩)) ∧
      (∀ z r, (∑ s, (label q 3 N (rep z) r s).val) = (coarse (cell r)).val) ∧
      (∀ z r, fourthLeftTag (label q 3 N (rep z) r) = (E.symm z).val r) ∧
      ∀ mask : Global cell p m → Prop,
        Fintype.card {a : Global cell p m // mask a} =
          Fintype.card {z : Blocks p m // mask (E.symm z)} := by
  classical
  obtain ⟨E, hE⟩ := profile_equiv cell p m positions hcell
  have hrep (z : Blocks p m) := atomic_representative.{u} q hq
    (fun r ↦ coarse (cell r)) (E.symm z).val
    (global_supported cell p m coarse hsupport (E.symm z))
  choose rep hgrade htag using hrep
  refine ⟨E, rep, hE, hgrade, htag, ?_⟩
  intro mask
  exact Fintype.card_congr
    (E.subtypeEquiv (fun a ↦ by simp only [E.symm_apply_apply]))

/-- The selected-owner predicate is a predicate of the same available blocks,
independent of the chosen atomic representative. -/
theorem selected_mask_descends
    {C : Type*} [Fintype C] [DecidableEq C] {N R : ℕ}
    (q : ℕ) (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → Fin 5 → ℕ) (j : Fin R)
    (p : C → IntegerZSplitProfile 5) (m : C → ℕ)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (E : Global (component j) p m ≃ Blocks p m)
    (rep : Blocks p m → WordIndex.{u} q 3 N)
    (hgrade : ∀ z, Graded component shape j 2 (label q 3 N (rep z)))
    (htag : ∀ z r, fourthLeftTag (label q 3 N (rep z) r) = (E.symm z).val r) :
    (∀ z, DWZSimultaneous.Profile component fourthLeftTag mu j 2
      (label q 3 N (rep z))) ∧
    ∀ (w : WordIndex.{u} q 3 N) (z : Blocks p m),
      Graded component shape j 2 (label q 3 N w) →
      (∀ r, fourthLeftTag (label q 3 N w r) = (E.symm z).val r) →
      ((Graded component shape j 2 (label q 3 N w) ∧
        DWZSimultaneous.Profile component fourthLeftTag mu j 2 (label q 3 N w) ∧
        ∀ j', ZCompatible component shape fourthLeftTag mu j' (label q 3 N w) → j' = j) ↔
      ∀ j', ZCompatible component shape fourthLeftTag mu j'
        (label q 3 N (rep z)) → j' = j) := by
  have hprofile (z : Blocks p m) :
      DWZSimultaneous.Profile component fourthLeftTag mu j 2 (label q 3 N (rep z)) := by
    intro c a
    simp only [htag, hmu]
    exact (E.symm z).property c a
  refine ⟨hprofile, ?_⟩
  intro w z hw hz
  have hg : ∀ r, (∑ s, (label q 3 N w r s).val) =
      ∑ s, (label q 3 N (rep z) r s).val :=
    fun r ↦ (hw r).trans ((hgrade z r).symm)
  have ht : ∀ r, fourthLeftTag (label q 3 N w r) =
      fourthLeftTag (label q 3 N (rep z) r) :=
    fun r ↦ (hz r).trans ((htag z r).symm)
  obtain ⟨_, hp, hc, _⟩ :=
    mme_dwz_fine_block_masks_depend_only_on_coarse_and_profile_labels
      component shape fourthLeftTag mu (label q 3 N w) (label q 3 N (rep z)) hg ht
  have hwp := (hp j 2).mpr (hprofile z)
  simp only [hw, hwp, true_and, hc]

end MME.DWZFourthBlockBridge

namespace MME.DWZProfileWitness

theorem prescribed_block_nonempty {t : ℕ} (p : IntegerZSplitProfile t) (m : ℕ) :
    Nonempty {w : PowIndex (Fin t) (p.length m) // prescribedZWord id p m w} := by
  classical
  have hc : Fintype.card (Σ a : Fin t, Fin (p.count a * m)) = p.length m := by
    simp only [Fintype.card_sigma, Fintype.card_fin, ← Finset.sum_mul,
      p.count_sum, IntegerZSplitProfile.length]
  let e : Fin (p.length m) ≃ (Σ a : Fin t, Fin (p.count a * m)) :=
    (Fintype.equivFinOfCardEq hc).symm
  have hcount (a : Fin t) :
      Fintype.card {r : Fin (p.length m) // (e r).1 = a} = p.count a * m := by
    let f : Fin (p.count a * m) → {r : Fin (p.length m) // (e r).1 = a} :=
      fun r ↦ ⟨e.symm ⟨a, r⟩, by simp⟩
    have hf : Function.Bijective f := by
      constructor
      · intro r s hrs
        have he : (⟨a, r⟩ : Σ a : Fin t, Fin (p.count a * m)) = ⟨a, s⟩ :=
          e.symm.injective (congrArg Subtype.val hrs)
        exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
      · intro x
        obtain ⟨⟨a', r⟩, hr⟩ := e.symm.surjective x.val
        have ha : a' = a := by
          have hh := x.property
          rw [← hr, e.apply_symm_apply] at hh
          exact hh
        subst a'
        exact ⟨r, Subtype.ext hr⟩
    simpa only [Fintype.card_fin] using (Fintype.card_of_bijective hf).symm
  refine ⟨⟨PowIndex.ofFun (p.length m) (fun r ↦ (e r).1), ?_⟩⟩
  intro a
  simpa only [leftGradeCount, PowIndex.get_ofFun, id_eq, Fintype.card_subtype] using hcount a

theorem fourth_coordinate_nonempty (q : ℕ) (hq : 0 < q) (k : Fin 9)
    (p : IntegerZSplitProfile 5) (m : ℕ)
    (hsupport : ∀ a, 0 < p.count a → a.val ≤ k.val ∧ k.val ≤ a.val + 4) :
    Nonempty {w : PowIndex
      (ULift.{u} {x : (Fin (q+2) × Fin (q+2)) × (Fin (q+2) × Fin (q+2)) //
        cwFourthPairGrade q x = k}) (p.length m) //
      prescribedZWord (fun x ↦ cwSquarePairGrade q x.down.val.1) p m w} := by
  classical
  obtain ⟨z⟩ := prescribed_block_nonempty p m
  have hs (r : Fin (p.length m)) :
      (PowIndex.get _ z.val r).val ≤ k.val ∧
        k.val ≤ (PowIndex.get _ z.val r).val + 4 := by
    have hp : 0 < leftGradeCount id z.val (PowIndex.get _ z.val r) := by
      apply Finset.card_pos.mpr
      exact ⟨r, by simp⟩
    rw [z.property] at hp
    exact hsupport _ (Nat.pos_of_mul_pos_right hp)
  have hx (r : Fin (p.length m)) :=
    (mme_CW_fourth_left_grade_fiber_nonempty_iff q hq k (PowIndex.get _ z.val r)).2 (hs r)
  choose x hxgrade hxleft using hx
  let f := fun r ↦ (ULift.up (⟨x r, hxgrade r⟩ :
    {x : (Fin (q+2) × Fin (q+2)) × (Fin (q+2) × Fin (q+2)) //
      cwFourthPairGrade q x = k}))
  refine ⟨⟨PowIndex.ofFun (p.length m) f, ?_⟩⟩
  intro a
  simpa only [leftGradeCount, PowIndex.get_ofFun, f, hxleft, id_eq] using z.property a

end MME.DWZProfileWitness

theorem solution
    {C : Type*} [Fintype C] [DecidableEq C] {N R : ℕ}
    (q : ℕ) (hq : 0 < q)
    (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → Fin 5 → ℕ) (j : Fin R)
    (p : C → IntegerZSplitProfile 5) (m : C → ℕ) (coarse : C → Fin 9)
    (hcoarse : ∀ c, shape c 2 = (coarse c).val)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (positions : Fin N ≃ Σ c, Fin ((p c).length (m c)))
    (hcell : ∀ c r, component j (positions.symm ⟨c, r⟩) = c)
    (hsupport : ∀ c a, 0 < (p c).count a →
      a.val ≤ (coarse c).val ∧ (coarse c).val ≤ a.val + 4) :
    let Global := {a : Fin N → Fin 5 // ∀ c z,
      Fintype.card {r : Fin N // component j r = c ∧ a r = z} =
        (p c).count z * m c}
    let Block := (c : C) → {w : PowIndex (Fin 5) ((p c).length (m c)) //
      prescribedZWord id (p c) (m c) w}
    let Coord := (c : C) → {w : PowIndex
      (ULift.{u} {x : (Fin (q+2) × Fin (q+2)) × (Fin (q+2) × Fin (q+2)) //
        cwFourthPairGrade q x = coarse c}) ((p c).length (m c)) //
      prescribedZWord (fun x ↦ cwSquarePairGrade q x.down.val.1) (p c) (m c) w}
    Nonempty Block ∧ Nonempty Coord ∧
    ∃ E : Global ≃ Block, ∃ rep : Block → WordIndex.{u} q 3 N,
      Fintype.card Block ≤ 2 ^ (N * 3) ∧
      (∀ a c r, PowIndex.get _ (E a c).val r = a.val (positions.symm ⟨c, r⟩)) ∧
      (∀ z, Graded component shape j 2 (label q 3 N (rep z)) ∧
        DWZSimultaneous.Profile component fourthLeftTag mu j 2 (label q 3 N (rep z))) ∧
      (∀ z r, fourthLeftTag (label q 3 N (rep z) r) = (E.symm z).val r) ∧
      (∀ mask : Global → Prop,
        Fintype.card {a : Global // mask a} =
          Fintype.card {z : Block // mask (E.symm z)}) ∧
      (∀ w : WordIndex.{u} q 3 N,
        DWZSimultaneous.Profile component fourthLeftTag mu j 2 (label q 3 N w) →
        ∃! z : Block, ∀ r, fourthLeftTag (label q 3 N w r) = (E.symm z).val r) ∧
      ∀ (w : WordIndex.{u} q 3 N) (z : Block),
        Graded component shape j 2 (label q 3 N w) →
        (∀ r, fourthLeftTag (label q 3 N w r) = (E.symm z).val r) →
        ((Graded component shape j 2 (label q 3 N w) ∧
          DWZSimultaneous.Profile component fourthLeftTag mu j 2 (label q 3 N w) ∧
          ∀ j', ZCompatible component shape fourthLeftTag mu j'
            (label q 3 N w) → j' = j) ↔
          ∀ j', ZCompatible component shape fourthLeftTag mu j'
            (label q 3 N (rep z)) → j' = j) := by
  classical
  dsimp only
  refine ⟨⟨fun c ↦ Classical.choice (DWZProfileWitness.prescribed_block_nonempty (p c) (m c))⟩,
    ⟨fun c ↦ Classical.choice (DWZProfileWitness.fourth_coordinate_nonempty.{u}
      q hq (coarse c) (p c) (m c) (hsupport c))⟩, ?_⟩
  obtain ⟨E, rep, hE, hg, ht, hm⟩ :=
    DWZFourthBlockBridge.actual_block_representatives.{u} q hq (component j)
      p m coarse positions hcell hsupport
  have hgrade (z) : Graded component shape j 2 (label q 3 N (rep z)) := by
    intro r
    rw [hcoarse]
    exact hg z r
  obtain ⟨hp, hmask⟩ := DWZFourthBlockBridge.selected_mask_descends q component shape
    mu j p m hmu E rep hgrade ht
  have hcard : Fintype.card (DWZFourthBlockBridge.Blocks p m) ≤ 2 ^ (N * 3) := by
    calc
      _ = Fintype.card (DWZFourthBlockBridge.Global (component j) p m) :=
        (Fintype.card_congr E).symm
      _ ≤ Fintype.card (Fin N → Fin 5) := Fintype.card_subtype_le _
      _ = 5 ^ N := by simp
      _ ≤ 8 ^ N := Nat.pow_le_pow_left (by decide) N
      _ = 2 ^ (N * 3) := by rw [Nat.mul_comm N 3, pow_mul]; rfl
  refine ⟨E, rep, hcard, hE, fun z ↦ ⟨hgrade z, hp z⟩, ht, hm, ?_, hmask⟩
  intro w hw
  let a : DWZFourthBlockBridge.Global (component j) p m :=
    ⟨fun r ↦ fourthLeftTag (label q 3 N w r), by
      intro c z
      rw [← hmu]
      exact hw c z⟩
  refine ⟨E a, ?_, ?_⟩
  · intro r
    simp only [E.symm_apply_apply]
    rfl
  · intro z hz
    apply E.symm.injective
    rw [E.symm_apply_apply]
    apply Subtype.ext
    funext r
    exact (hz r).symm
