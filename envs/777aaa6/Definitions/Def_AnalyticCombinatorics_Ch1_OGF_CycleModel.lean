-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_CycleModel
-- name    : AnalyticCombinatorics_Ch1_OGF_CycleModel
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:06:40.54244+00:00
-- url     : https://prove2.me/theorems/8d2d57e0-ee95-4924-a799-eceb0f2a9a18
-- title:
--   Finite words and rotation necklaces
-- statement:
--   A component carries a natural size at most n and an object of that size. A word indexed by a finite type assigns components whose sizes sum to n. The cyclic group ZMod k rotates words indexed by ZMod k; necklaces are its orbit quotient. Quotient words record periodic blocks, and the finite equivalences compare fixed words with words on the quotient index set.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/CycleModel.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.2 — Cycle model, fixed-point layer

This file builds the bounded word model for cycles and proves the fixed-point
cardinality used by Burnside in the next layer.
-/

namespace AnalyticCombinatorics.Ch1

open scoped BigOperators

universe u

/-- Components of size at most `n`, packed with their size. -/
def CompUpTo (C : CombClass) (n : ℕ) : Type :=
  Σ m : Fin (n + 1), C.Obj m.val

/-- The size carried by a bounded component. -/
def compSize {C : CombClass} {n : ℕ} (c : CompUpTo C n) : ℕ :=
  c.1.val

private def shrinkCompUpTo {C : CombClass} {m n : ℕ}
    (c : CompUpTo C n) (h : compSize c ≤ m) : CompUpTo C m :=
  ⟨⟨c.1.val, Nat.lt_succ_of_le h⟩, c.2⟩

private def widenCompUpTo {C : CombClass} {m n : ℕ}
    (h : m ≤ n) (c : CompUpTo C m) : CompUpTo C n :=
  ⟨Fin.castLE (Nat.succ_le_succ h) c.1, c.2⟩

@[simp] private lemma compSize_shrinkCompUpTo {C : CombClass} {m n : ℕ}
    (c : CompUpTo C n) (h : compSize c ≤ m) :
    compSize (shrinkCompUpTo c h) = compSize c :=
  rfl

@[simp] private lemma compSize_widenCompUpTo {C : CombClass} {m n : ℕ}
    (h : m ≤ n) (c : CompUpTo C m) :
    compSize (widenCompUpTo h c) = compSize c :=
  rfl

private lemma widenCompUpTo_shrinkCompUpTo {C : CombClass} {m n : ℕ}
    (hmn : m ≤ n) (c : CompUpTo C n) (h : compSize c ≤ m) :
    widenCompUpTo hmn (shrinkCompUpTo c h) = c := by
  cases c with
  | mk i obj =>
      apply Sigma.ext
      · ext
        rfl
      · simp [widenCompUpTo, shrinkCompUpTo]

private lemma shrinkCompUpTo_widenCompUpTo {C : CombClass} {m n : ℕ}
    (hmn : m ≤ n) (c : CompUpTo C m)
    (h : compSize (widenCompUpTo hmn c) ≤ m) :
    shrinkCompUpTo (widenCompUpTo hmn c) h = c := by
  cases c with
  | mk i obj =>
      apply Sigma.ext
      · ext
        rfl
      · simp [widenCompUpTo, shrinkCompUpTo]

/-- Words over a finite index type whose component sizes sum to `n`. -/
def WordOn (C : CombClass) (n : ℕ) (ι : Type u) [Fintype ι] :=
  { f : ι → CompUpTo C n // ∑ i, compSize (f i) = n }

/-- Words indexed by `ZMod k`; these are the length-`k` rotation carriers. -/
abbrev Word (C : CombClass) (n k : ℕ) [Fintype (ZMod k)] : Type :=
  WordOn C n (ZMod k)

/-- Block words indexed by `Fin g`. -/
abbrev BlockWord (C : CombClass) (n g : ℕ) : Type :=
  WordOn C n (Fin g)

noncomputable instance instFintypeCompUpTo (C : CombClass) (n : ℕ) :
    Fintype (CompUpTo C n) := by
  classical
  change Fintype (Σ m : Fin (n + 1), C.Obj m.val)
  infer_instance

noncomputable instance instFintypeWordOn
    (C : CombClass) (n : ℕ) (ι : Type u) [Fintype ι] :
    Fintype (WordOn C n ι) := by
  classical
  change Fintype { f : ι → CompUpTo C n // ∑ i, compSize (f i) = n }
  infer_instance

/-- Rotation of `ZMod k`-indexed words by right translation. -/
noncomputable instance instAddActionWord
    (C : CombClass) (n k : ℕ) [NeZero k] :
    AddAction (ZMod k) (Word C n k) where
  vadd a w :=
    ⟨fun x => w.1 (x + a), by
      simpa using
        ((Equiv.sum_comp (Equiv.addRight a)
          (fun x : ZMod k => compSize (w.1 x))).trans w.2)⟩
  zero_vadd := by
    intro w
    apply Subtype.ext
    funext x
    change w.1 (x + 0) = w.1 x
    rw [add_zero]
  add_vadd := by
    intro a b w
    apply Subtype.ext
    funext x
    change w.1 (x + (a + b)) = w.1 ((x + a) + b)
    rw [add_assoc]

@[simp] lemma word_vadd_apply
    (C : CombClass) (n k : ℕ) [NeZero k]
    (a x : ZMod k) (w : Word C n k) :
    ((a +ᵥ w : Word C n k).1 x) = w.1 (x + a) :=
  rfl

lemma mem_fixedBy_rotation
    (C : CombClass) (n k : ℕ) [NeZero k]
    (a : ZMod k) (w : Word C n k) :
    w ∈ AddAction.fixedBy (Word C n k) a ↔
      ∀ x : ZMod k, w.1 (x + a) = w.1 x := by
  rw [AddAction.mem_fixedBy]
  constructor
  · intro h x
    simpa [word_vadd_apply] using congr_fun (congr_arg Subtype.val h) x
  · intro h
    apply Subtype.ext
    funext x
    simpa [word_vadd_apply] using h x

noncomputable instance instFintypeFixedByWord
    (C : CombClass) (n k : ℕ) [NeZero k] (a : ZMod k) :
    Fintype (AddAction.fixedBy (Word C n k) a) := by
  classical
  change Fintype { w : Word C n k // w ∈ AddAction.fixedBy (Word C n k) a }
  infer_instance

noncomputable def quotientFiberEquivZMultiples
    (k : ℕ) [NeZero k] (a : ZMod k)
    (q : ZMod k ⧸ AddSubgroup.zmultiples a) :
    { x : ZMod k // (x : ZMod k ⧸ AddSubgroup.zmultiples a) = q } ≃
      AddSubgroup.zmultiples a where
  toFun x :=
    ⟨x.1 - q.out, by
      have hxq : (x.1 : ZMod k ⧸ AddSubgroup.zmultiples a) =
          (q.out : ZMod k ⧸ AddSubgroup.zmultiples a) :=
        x.2.trans (Quotient.out_eq' q).symm
      exact (QuotientAddGroup.eq_iff_sub_mem.mp hxq)⟩
  invFun h :=
    ⟨q.out + h.1, by
      have hmem : q.out + h.1 - q.out ∈ AddSubgroup.zmultiples a := by
        convert h.2 using 1
        simp [sub_eq_add_neg, add_assoc, add_left_comm]
      have hquot : ((q.out + h.1 : ZMod k) :
          ZMod k ⧸ AddSubgroup.zmultiples a) =
          (q.out : ZMod k ⧸ AddSubgroup.zmultiples a) :=
        QuotientAddGroup.eq_iff_sub_mem.mpr hmem
      exact hquot.trans (Quotient.out_eq' q)⟩
  left_inv x := by
    apply Subtype.ext
    simp [sub_eq_add_neg, add_left_comm]
  right_inv h := by
    apply Subtype.ext
    simp [sub_eq_add_neg, add_assoc, add_comm]

lemma card_quotientFiber_zmultiples
    (k : ℕ) [NeZero k] (a : ZMod k)
    (q : ZMod k ⧸ AddSubgroup.zmultiples a) :
    Fintype.card
      { x : ZMod k // (x : ZMod k ⧸ AddSubgroup.zmultiples a) = q } =
      addOrderOf a := by
  rw [← Fintype.card_zmultiples (x := a)]
  exact Fintype.card_congr (quotientFiberEquivZMultiples k a q)

lemma sum_quotient_mk_zmultiples
    (k : ℕ) [NeZero k] (a : ZMod k)
    (φ : (ZMod k ⧸ AddSubgroup.zmultiples a) → ℕ) :
    (∑ x : ZMod k, φ (x : ZMod k ⧸ AddSubgroup.zmultiples a)) =
      addOrderOf a * ∑ q : ZMod k ⧸ AddSubgroup.zmultiples a, φ q := by
  classical
  let Q := ZMod k ⧸ AddSubgroup.zmultiples a
  have hfiber := Fintype.sum_fiberwise
    (fun x : ZMod k => (x : Q))
    (fun x : ZMod k => φ (x : Q))
  rw [← hfiber]
  calc
    (∑ q : Q, ∑ x : { x : ZMod k // (fun x : ZMod k => (x : Q)) x = q },
        φ (((x : ZMod k) : Q))) =
        ∑ q : Q, ∑ x : { x : ZMod k // (fun x : ZMod k => (x : Q)) x = q },
          φ q := by
          refine Finset.sum_congr rfl fun q _ => ?_
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [x.2]
    _ = ∑ q : Q,
        Fintype.card { x : ZMod k // (x : Q) = q } * φ q := by
          refine Finset.sum_congr rfl fun q _ => ?_
          simp
    _ = ∑ q : Q, addOrderOf a * φ q := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [card_quotientFiber_zmultiples]
    _ = addOrderOf a * ∑ q : Q, φ q := by
          rw [Finset.mul_sum]

lemma sum_periodic_eq_addOrderOf_mul_sum_lift
    (C : CombClass) (n k : ℕ) [NeZero k] (a : ZMod k)
    {f : ZMod k → CompUpTo C n} (hf : Function.Periodic f a) :
    (∑ x : ZMod k, compSize (f x)) =
      addOrderOf a *
        ∑ q : ZMod k ⧸ AddSubgroup.zmultiples a, compSize (hf.lift q) := by
  simpa [Function.Periodic.lift_coe] using
    (sum_quotient_mk_zmultiples k a
      (fun q : ZMod k ⧸ AddSubgroup.zmultiples a => compSize (hf.lift q)))

def QuotRaw (C : CombClass) (n k : ℕ) [NeZero k] (a : ZMod k) : Type :=
  { qf : (ZMod k ⧸ AddSubgroup.zmultiples a) → CompUpTo C n //
      addOrderOf a * (∑ q, compSize (qf q)) = n }

noncomputable def fixedBy_rotation_equiv_quotientRaw
    (C : CombClass) (n k : ℕ) [NeZero k] (a : ZMod k) :
    AddAction.fixedBy (Word C n k) a ≃ QuotRaw C n k a where
  toFun w :=
    let hf : Function.Periodic w.1.1 a :=
      (mem_fixedBy_rotation C n k a w.1).mp w.2
    ⟨hf.lift, by
      exact (sum_periodic_eq_addOrderOf_mul_sum_lift C n k a hf).symm.trans w.1.2⟩
  invFun qf :=
    let word : Word C n k :=
      ⟨fun x : ZMod k => qf.1 (x : ZMod k ⧸ AddSubgroup.zmultiples a), by
        exact (sum_quotient_mk_zmultiples k a
          (fun q : ZMod k ⧸ AddSubgroup.zmultiples a => compSize (qf.1 q))).trans qf.2⟩
    ⟨word, by
      rw [mem_fixedBy_rotation C n k a word]
      intro x
      have hquot : ((x + a : ZMod k) : ZMod k ⧸ AddSubgroup.zmultiples a) =
          (x : ZMod k ⧸ AddSubgroup.zmultiples a) := by
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        convert (AddSubgroup.mem_zmultiples a) using 1
        simp [sub_eq_add_neg, add_assoc, add_comm]
      exact congrArg qf.1 hquot⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    simp [Function.Periodic.lift_coe]
  right_inv qf := by
    apply Subtype.ext
    funext q
    refine Quotient.inductionOn' q ?_
    intro x
    simp [Function.Periodic.lift_coe]

lemma le_sum_univ_nat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (i : ι) :
    f i ≤ ∑ j, f j := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)]
  exact Nat.le_add_right (f i) _

noncomputable def quotientRaw_equiv_wordOn_of_dvd
    (C : CombClass) (n k : ℕ) [NeZero k] (a : ZMod k)
    (hdiv : addOrderOf a ∣ n) :
    QuotRaw C n k a ≃
      WordOn C (n / addOrderOf a)
        (ZMod k ⧸ AddSubgroup.zmultiples a) where
  toFun qf := by
    classical
    have hdpos : 0 < addOrderOf a := addOrderOf_pos a
    have hsum :
        (∑ q : ZMod k ⧸ AddSubgroup.zmultiples a, compSize (qf.1 q)) =
          n / addOrderOf a :=
      Nat.eq_div_of_mul_eq_right (Nat.ne_of_gt hdpos) qf.2
    refine ⟨fun q => shrinkCompUpTo (qf.1 q) ?_, ?_⟩
    · exact (le_sum_univ_nat
        (fun q : ZMod k ⧸ AddSubgroup.zmultiples a => compSize (qf.1 q)) q).trans
        (le_of_eq hsum)
    · simpa using hsum
  invFun w := by
    classical
    let hle : n / addOrderOf a ≤ n := Nat.div_le_self n (addOrderOf a)
    refine ⟨fun q => widenCompUpTo hle (w.1 q), ?_⟩
    have hsum :
        (∑ q : ZMod k ⧸ AddSubgroup.zmultiples a,
            compSize (widenCompUpTo hle (w.1 q))) =
          n / addOrderOf a := by
      simpa using w.2
    calc
      addOrderOf a *
          (∑ q : ZMod k ⧸ AddSubgroup.zmultiples a,
            compSize (widenCompUpTo hle (w.1 q))) =
          addOrderOf a * (n / addOrderOf a) := by rw [hsum]
      _ = n := Nat.mul_div_cancel' hdiv
  left_inv qf := by
    classical
    apply Subtype.ext
    funext q
    have hdpos : 0 < addOrderOf a := addOrderOf_pos a
    have hsum :
        (∑ q : ZMod k ⧸ AddSubgroup.zmultiples a, compSize (qf.1 q)) =
          n / addOrderOf a :=
      Nat.eq_div_of_mul_eq_right (Nat.ne_of_gt hdpos) qf.2
    exact widenCompUpTo_shrinkCompUpTo
      (Nat.div_le_self n (addOrderOf a)) (qf.1 q)
      ((le_sum_univ_nat
        (fun q : ZMod k ⧸ AddSubgroup.zmultiples a => compSize (qf.1 q)) q).trans
        (le_of_eq hsum))
  right_inv w := by
    classical
    apply Subtype.ext
    funext q
    exact shrinkCompUpTo_widenCompUpTo
      (Nat.div_le_self n (addOrderOf a)) (w.1 q)
      ((le_sum_univ_nat
        (fun q : ZMod k ⧸ AddSubgroup.zmultiples a => compSize (w.1 q)) q).trans
        (le_of_eq w.2))

noncomputable def fixedBy_rotation_equiv_word_quotient
    (C : CombClass) (n k : ℕ) [NeZero k] (a : ZMod k)
    (hdiv : addOrderOf a ∣ n) :
    AddAction.fixedBy (Word C n k) a ≃
      WordOn C (n / addOrderOf a)
        (ZMod k ⧸ AddSubgroup.zmultiples a) :=
  (fixedBy_rotation_equiv_quotientRaw C n k a).trans
    (quotientRaw_equiv_wordOn_of_dvd C n k a hdiv)

noncomputable def wordOn_equiv_fin_of_card
    (C : CombClass) (n g : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = g) :
    WordOn C n ι ≃ BlockWord C n g := by
  classical
  let e : ι ≃ Fin g := Fintype.equivFinOfCardEq hcard
  refine
    { toFun := fun w =>
        ⟨fun i : Fin g => w.1 (e.symm i), by
          simpa using
            ((Equiv.sum_comp e.symm
              (fun i : ι => compSize (w.1 i))).trans w.2)⟩
      invFun := fun w =>
        ⟨fun i : ι => w.1 (e i), by
          simpa using
            ((Equiv.sum_comp e
              (fun i : Fin g => compSize (w.1 i))).trans w.2)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    apply Subtype.ext
    funext i
    simp [e]
  · intro w
    apply Subtype.ext
    funext i
    simp [e]

abbrev necklaces_k (C : CombClass) (n k : ℕ) [NeZero k] : Type :=
  Quotient (AddAction.orbitRel (ZMod k) (Word C n k))

noncomputable instance instFintypeNecklaces_k
    (C : CombClass) (n k : ℕ) [NeZero k] :
    Fintype (necklaces_k C n k) := by
  classical
  infer_instance

end AnalyticCombinatorics.Ch1


