-- Prove2me | solution 1 for mme_dwz_recursive_target_words_preserve_original_parent_profiles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T15:29:40.413517+00:00
-- url     : https://prove2.me/submissions/900d1373-97f9-4874-ba57-85618a626036

import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_recursive_yz_hash_filter
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.CompleteSplit.CWFourth
open scoped Classical
universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace MME.DWZC1ParentKeep

theorem count_comp {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (w : Fin n → A) (g : A → B) (b : B) :
    RecursiveThinSplit.count (g ∘ w) b =
      ∑ a : {a : A // g a = b}, RecursiveThinSplit.count w a.val := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin n)) (Finset.univ.filter (fun a ↦ g a = b)) w
  calc
    _ = ∑ a ∈ Finset.univ.filter (fun a ↦ g a = b), RecursiveThinSplit.count w a := by
      simpa only [RecursiveThinSplit.count, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.comp_apply] using h.symm
    _ = _ := Finset.sum_subtype _ (by simp) (RecursiveThinSplit.count w)

theorem joint_implies_marginal {half n : ℕ} {parent : Fin 3 → ℕ}
    (a : Fin n → RecursiveThinSplit.Split half parent)
    (m : RecursiveThinSplit.Split half parent → ℕ)
    (ha : RecursiveThinSplit.HasJointCounts a m) :
    RecursiveThinSplit.HasMarginalCounts a m := by
  intro i j
  exact (count_comp a (fun c ↦ c.val i) j).trans
    (Finset.sum_congr rfl (fun c _ ↦ ha c.val))

theorem target_marginal {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m) :
    ∀ r, RecursiveThinSplit.HasMarginalCounts (a r) (m r) := by
  have h := (Finset.mem_filter.mp ha).2
  exact fun r ↦ joint_implies_marginal (a r) (m r) (h r)

/-- Exact coarse parent grades and the original left-child histogram in each
region's retained mode; rotations transport the mode without changing its profile. -/
def ParentKeep {R ell : ℕ} (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (keptMode : Fin R → Fin 3) (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (i : Fin 3) (f : Position n → CompleteWord ell) : Prop :=
  (∀ r t, CWCells.grade (f ⟨r,t,0⟩) + CWCells.grade (f ⟨r,t,1⟩) = parent r i) ∧
  (∀ r, i = keptMode r → ∀ j : Fin 5,
    (Finset.univ.filter (fun t : Fin (n r) ↦
      CWCells.grade (f ⟨r,t,0⟩) = j.val)).card = (p r).count j * scale r)

theorem graded_parentKeep {R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 8)
    (m : ∀ r, RecursiveThinSplit.Split 4 (parent r) → ℕ)
    (keptMode : Fin R → Fin 3)
    (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (hprofile : ∀ r j, (∑ c : {c : RecursiveThinSplit.Split 4 (parent r) // c.val (keptMode r) = j},
      m r c.val) = (p r).count j * scale r)
    (a : Address 4 R parent n) (ha : a ∈ RecursiveXHash.target m)
    (i : Fin 3) (f : Position n → CompleteWord ell)
    (hf : Graded htotal i a f) : ParentKeep parent n keptMode p scale i f := by
  have hleft (r : Fin R) (t : Fin (n r)) :
      CWCells.grade (f ⟨r,t,0⟩) = ((a r t).val i).val := by
    simpa only [CWCells.grade, fullCell, if_pos rfl] using hf ⟨r,t,0⟩
  have hright (r : Fin R) (t : Fin (n r)) :
      CWCells.grade (f ⟨r,t,1⟩) = parent r i - ((a r t).val i).val := by
    simpa only [CWCells.grade, fullCell, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero,
      if_false, complement] using hf ⟨r,t,1⟩
  constructor
  · intro r t
    rw [hleft,hright]
    exact Nat.add_sub_of_le ((a r t).property.2 i)
  · intro r hi j
    have hcounts := target_marginal m a ha r (keptMode r) j
    have heq : (Finset.univ.filter (fun t : Fin (n r) ↦
        CWCells.grade (f ⟨r,t,0⟩) = j.val)) =
        Finset.univ.filter (fun t : Fin (n r) ↦ (a r t).val (keptMode r) = j) := by
      apply Finset.filter_congr
      intro t _
      rw [hleft,hi]
      exact Fin.val_inj
    exact (congrArg Finset.card heq).trans (hcounts.trans (hprofile r j))

theorem parent_holes_empty {R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 8)
    (m : ∀ r, RecursiveThinSplit.Split 4 (parent r) → ℕ)
    (keptMode : Fin R → Fin 3)
    (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (hprofile : ∀ r j, (∑ c : {c : RecursiveThinSplit.Split 4 (parent r) // c.val (keptMode r) = j},
      m r c.val) = (p r).count j * scale r)
    (a : Address 4 R parent n) (ha : a ∈ RecursiveXHash.target m)
    (i : Fin 3) (mu : Cell 4 R parent → CompleteWord ell → ℕ) :
    (unbrokenWords htotal i a mu).filter
      (fun f ↦ ¬ ParentKeep parent n keptMode p scale i f) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  have h := Finset.mem_filter.mp hf
  have hgraded := (Finset.mem_filter.mp h.1).2.1
  exact h.2 (graded_parentKeep htotal m keptMode p scale hprofile a ha i f hgraded)

def parentCoordinate {R L : ℕ} {n : Fin R → ℕ} (q : ℕ)
    (positions : Fin L ≃ Position n) (x : CWCells.WordIndex.{u} q 2 L)
    (r : Fin R) (t : Fin (n r)) : Coordinate q :=
  (((x (finProdFinEquiv (positions.symm ⟨r,t,0⟩, (0 : Fin 2)))).down,
     (x (finProdFinEquiv (positions.symm ⟨r,t,0⟩, (1 : Fin 2)))).down),
    ((x (finProdFinEquiv (positions.symm ⟨r,t,1⟩, (0 : Fin 2)))).down,
     (x (finProdFinEquiv (positions.symm ⟨r,t,1⟩, (1 : Fin 2)))).down))

theorem grade_two (w : CompleteWord 2) :
    CWCells.grade w = (w 0).val + (w 1).val := by
  change (∑ r : Fin 2, (w r).val) = _
  exact Fin.sum_univ_two _

theorem parentCoordinate_left {R L : ℕ} {n : Fin R → ℕ} (q : ℕ)
    (positions : Fin L ≃ Position n) (x : CWCells.WordIndex.{u} q 2 L)
    (r : Fin R) (t : Fin (n r)) :
    (cwSquarePairGrade q (parentCoordinate q positions x r t).1).val =
      CWCells.grade (CWCells.label q 2 L positions x ⟨r,t,0⟩) := by
  rw [grade_two]
  rfl

theorem parentCoordinate_total {R L : ℕ} {n : Fin R → ℕ} (q : ℕ)
    (positions : Fin L ≃ Position n) (x : CWCells.WordIndex.{u} q 2 L)
    (r : Fin R) (t : Fin (n r)) :
    (StothersFourth.cwFourthPairGrade q (parentCoordinate q positions x r t)).val =
      CWCells.grade (CWCells.label q 2 L positions x ⟨r,t,0⟩) +
        CWCells.grade (CWCells.label q 2 L positions x ⟨r,t,1⟩) := by
  rw [grade_two,grade_two]
  rfl

/-- Every actually available atomic coordinate word in a graded target copy
packs into the original canonical prescribed parent word in its retained mode. -/
theorem label_original_prescribed_parent {R L : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (q : ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 8)
    (m : ∀ r, RecursiveThinSplit.Split 4 (parent r) → ℕ)
    (keptMode : Fin R → Fin 3)
    (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (hprofile : ∀ r j, (∑ c : {c : RecursiveThinSplit.Split 4 (parent r) // c.val (keptMode r) = j},
      m r c.val) = (p r).count j * scale r)
    (a : Address 4 R parent n) (ha : a ∈ RecursiveXHash.target m)
    (positions : Fin L ≃ Position n) (x : CWCells.WordIndex.{u} q 2 L)
    (i : Fin 3) (hx : Graded htotal i a (CWCells.label q 2 L positions x))
    (r : Fin R) (hi : i = keptMode r) (Z : Fin 9) (hZ : parent r i = Z.val)
    (hlen : n r = (p r).length (scale r)) :
    ∃ w : PowIndex (LiftedCoarseCoordinate.{u} q Z) ((p r).length (scale r)),
      prescribedZWord (fun b : LiftedCoarseCoordinate.{u} q Z ↦
        cwSquarePairGrade q b.down.val.1) (p r) (scale r) w ∧
      ∀ t, (PowIndex.get _ w t).down.val =
        parentCoordinate q positions x r (Fin.cast hlen.symm t) := by
  classical
  have hkeep := graded_parentKeep htotal m keptMode p scale hprofile a ha i
    (CWCells.label q 2 L positions x) hx
  let e : Fin ((p r).length (scale r)) ≃ Fin (n r) := finCongr hlen.symm
  let b : Fin ((p r).length (scale r)) → LiftedCoarseCoordinate.{u} q Z := fun t ↦
    ⟨⟨parentCoordinate q positions x r (e t), by
      apply Fin.ext
      exact (parentCoordinate_total q positions x r (e t)).trans
        ((hkeep.1 r (e t)).trans hZ)⟩⟩
  refine ⟨PowIndex.ofFun _ b, ?_, ?_⟩
  · intro j
    unfold leftGradeCount
    simp only [PowIndex.get_ofFun]
    have hcard : (Finset.univ.filter (fun t : Fin ((p r).length (scale r)) ↦
        cwSquarePairGrade q (b t).down.val.1 = j)).card =
        (Finset.univ.filter (fun t : Fin (n r) ↦
          CWCells.grade (CWCells.label q 2 L positions x ⟨r,t,0⟩) = j.val)).card := by
      apply Finset.card_bij (fun t _ ↦ e t)
      · intro t ht
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have h := congrArg Fin.val (Finset.mem_filter.mp ht).2
        exact (parentCoordinate_left q positions x r (e t)).symm.trans h
      · intro t _ s _ h
        exact e.injective h
      · intro t ht
        refine ⟨e.symm t, ?_, e.apply_symm_apply t⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Fin.ext
        change (cwSquarePairGrade q (parentCoordinate q positions x r (e (e.symm t))).1).val = _
        rw [e.apply_symm_apply, parentCoordinate_left]
        exact (Finset.mem_filter.mp ht).2
    exact hcard.trans (hkeep.2 r hi j)
  · intro t
    rw [PowIndex.get_ofFun]
    rfl

end MME.DWZC1ParentKeep

theorem solution
    (q R L : ℕ) (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 8)
    (m : ∀ r, RecursiveThinSplit.Split 4 (parent r) → ℕ)
    (keptMode : Fin R → Fin 3)
    (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (hprofile : ∀ r j,
      (∑ c : {c : RecursiveThinSplit.Split 4 (parent r) // c.val (keptMode r) = j},
        m r c.val) = (p r).count j * scale r)
    (a : Address 4 R parent n) (ha : a ∈ RecursiveXHash.target m)
    (positions : Fin L ≃ Position n) :
    let keep : ∀ ell, Fin 3 → (Position n → CompleteWord ell) → Prop := fun _ell i f ↦
      (∀ r t, CWCells.grade (f ⟨r,t,0⟩) + CWCells.grade (f ⟨r,t,1⟩) = parent r i) ∧
      (∀ r, i = keptMode r → ∀ j : Fin 5,
        (Finset.univ.filter (fun t : Fin (n r) ↦
          CWCells.grade (f ⟨r,t,0⟩) = j.val)).card = (p r).count j * scale r)
    (∀ ell i (mu : Cell 4 R parent → CompleteWord ell → ℕ),
      (unbrokenWords htotal i a mu).filter (fun f ↦ ¬ keep ell i f) = ∅) ∧
    ∀ (i : Fin 3) (x : CWCells.WordIndex.{u} q 2 L),
      Graded htotal i a (CWCells.label q 2 L positions x) →
      ∀ (r : Fin R), i = keptMode r →
      ∀ (Z : Fin 9), parent r i = Z.val →
      ∀ hlen : n r = (p r).length (scale r),
      ∃ w : PowIndex (LiftedCoarseCoordinate.{u} q Z) ((p r).length (scale r)),
        prescribedZWord (fun b : LiftedCoarseCoordinate.{u} q Z ↦
          cwSquarePairGrade q b.down.val.1) (p r) (scale r) w ∧
        ∀ t,
          let v := Fin.cast hlen.symm t
          (PowIndex.get _ w t).down.val =
            (((x (finProdFinEquiv (positions.symm ⟨r,v,0⟩, (0 : Fin 2)))).down,
               (x (finProdFinEquiv (positions.symm ⟨r,v,0⟩, (1 : Fin 2)))).down),
              ((x (finProdFinEquiv (positions.symm ⟨r,v,1⟩, (0 : Fin 2)))).down,
               (x (finProdFinEquiv (positions.symm ⟨r,v,1⟩, (1 : Fin 2)))).down)) := by
  dsimp only
  constructor
  · intro ell i mu
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have h := Finset.mem_filter.mp hf
    have hgraded := (Finset.mem_filter.mp h.1).2.1
    exact h.2 (MME.DWZC1ParentKeep.graded_parentKeep htotal m keptMode p scale
      hprofile a ha i f hgraded)
  · intro i x hx r hi Z hZ hlen
    exact MME.DWZC1ParentKeep.label_original_prescribed_parent q htotal m keptMode p scale
      hprofile a ha positions x i hx r hi Z hZ hlen
