-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledCyc
-- name    : AnalyticCombinatorics_Ch2_EGF_LabelledCyc
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:56:40.631002+00:00
-- url     : https://prove2.me/theorems/ba3c0043-c67e-4bb1-a469-913d0cd68be8
-- title:
--   Canonical rotations of labelled component cycles
-- statement:
--   A labelled cycle has at least one component. Its representative is an ordered labelled power whose first block contains the largest label, removing rotational ambiguity. The construction includes explicit label-subset decompositions, rooted-block data and finite equivalences relating a distinguished label in a cycle to a distinguished label in one component followed by a labelled sequence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledCyc.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch2 §II.2 — The labelled set ODE

This file contains the coefficient-level machinery for the differential equation
of the labelled set construction.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

@[simp] lemma rootBlockEquiv_card (n : ℕ) (S : Finset (Fin n)) :
    (rootBlockEquiv n S).val.card = S.card + 1 := by
  simp [rootBlockEquiv]

end AnalyticCombinatorics.Ch1



/-!
# Ch2 §II.2 — The labelled cycle construction

This file gives a concrete canonical-rotation model for labelled cycles.  A
nonempty labelled power represents a cycle by rotating it so that the first
block contains the largest label.  The transfer theorem is stated as the
defining differential equation

  `CYC(C)' = C' * SEQ(C)`, with zero constant term.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

private def lpowSuccRootBlock (C : CombClass) (n k : ℕ)
    (x : (C.lpow (k + 1)).Obj (n + 1)) : Finset (Fin (n + 1)) :=
  ((show (C.lprod (C.lpow k)).Obj (n + 1) from x).2.1 : Finset (Fin (n + 1)))

private def lpowSuccRootContainsLast (C : CombClass) (n k : ℕ)
    (x : (C.lpow (k + 1)).Obj (n + 1)) : Prop :=
  Fin.last n ∈ lpowSuccRootBlock C n k x

/-- The labelled cycle construction, represented by the canonical rotation whose
first block contains the largest label. -/
noncomputable def CombClass.lcyc (C : CombClass) : CombClass where
  Obj
    | 0 => Fin 0
    | n + 1 =>
        Σ k : Fin (n + 1),
          {x : (C.lpow ((k : ℕ) + 1)).Obj (n + 1) //
            lpowSuccRootContainsLast C n (k : ℕ) x}
  finObj
    | 0 => inferInstance
    | n + 1 => by
        classical
        infer_instance

private noncomputable def lprodObjEquivBySubset (A B : CombClass) (n : ℕ) :
    (A.lprod B).Obj n ≃
      Σ S : Finset (Fin n), A.Obj S.card × B.Obj (n - S.card) where
  toFun x := by
    rcases x with ⟨i, S, a, b⟩
    refine ⟨S, ?_, ?_⟩
    · simpa [S.property] using a
    · simpa [S.property] using b
  invFun x := by
    rcases x with ⟨S, a, b⟩
    let i : Fin (n + 1) :=
      ⟨S.card, Nat.lt_succ_of_le (by simpa [Fintype.card_fin] using S.card_le_univ)⟩
    exact ⟨i, ⟨S, rfl⟩, a, b⟩
  left_inv x := by
    rcases x with ⟨i, ⟨S, hS⟩, a, b⟩
    cases i with
    | mk iv hiv =>
        dsimp at hS ⊢
        subst iv
        rfl
  right_inv x := by
    rcases x with ⟨S, a, b⟩
    rfl

private abbrev RootedBlockData (C : CombClass) (n k : ℕ) :=
  Σ B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B},
    C.Obj B.val.card × (C.lpow k).Obj ((n + 1) - B.val.card)

private abbrev RootedSmallData (C : CombClass) (n k : ℕ) :=
  Σ S : Finset (Fin n), C.Obj (S.card + 1) × (C.lpow k).Obj (n - S.card)

private noncomputable def lpowSuccRootEquiv (C : CombClass) (n k : ℕ) :
    {x : (C.lpow (k + 1)).Obj (n + 1) // lpowSuccRootContainsLast C n k x} ≃
      RootedBlockData C n k := by
  let e : (C.lpow (k + 1)).Obj (n + 1) ≃
      (Σ B : Finset (Fin (n + 1)),
        C.Obj B.card × (C.lpow k).Obj ((n + 1) - B.card)) :=
    (Equiv.refl _).trans (lprodObjEquivBySubset C (C.lpow k) (n + 1))
  exact (e.subtypeEquiv (by
    intro x
    rcases x with ⟨i, S, a, t⟩
    rfl)).trans
      (Equiv.subtypeSigmaEquiv
        (fun B : Finset (Fin (n + 1)) =>
          C.Obj B.card × (C.lpow k).Obj ((n + 1) - B.card))
        (fun B => Fin.last n ∈ B))

private noncomputable def rootBlockDataEquiv (C : CombClass) (n k : ℕ) :
    RootedBlockData C n k ≃ RootedSmallData C n k :=
  Equiv.sigmaCongr (rootBlockEquiv n).symm fun B =>
    Equiv.prodCongr
      (Equiv.cast (by
        have hB : (rootBlockEquiv n ((rootBlockEquiv n).symm B)).val = B.val :=
          congrArg Subtype.val (Equiv.apply_symm_apply (rootBlockEquiv n) B)
        have hcard : B.val.card = ((rootBlockEquiv n).symm B).card + 1 := by
          rw [← hB, rootBlockEquiv_card]
        rw [hcard]))
      (Equiv.cast (by
        have hB : (rootBlockEquiv n ((rootBlockEquiv n).symm B)).val = B.val :=
          congrArg Subtype.val (Equiv.apply_symm_apply (rootBlockEquiv n) B)
        have hcard : B.val.card = ((rootBlockEquiv n).symm B).card + 1 := by
          rw [← hB, rootBlockEquiv_card]
        have hsize : (n + 1) - B.val.card = n - ((rootBlockEquiv n).symm B).card := by
          omega
        rw [hsize]))

/-- If `C₀ = ∅`, a nonempty `k`-fold labelled power of size `n` has `k ≤ n`. -/
lemma lpow_length_le_size_of_obj (C : CombClass) (hC : C.counts 0 = 0) :
    ∀ {k n : ℕ}, (C.lpow k).Obj n → k ≤ n := by
  intro k
  induction k with
  | zero =>
      intro n x
      omega
  | succ k ih =>
      intro n x
      change (C.lprod (C.lpow k)).Obj n at x
      rcases x with ⟨i, S, a, tail⟩
      have hi_pos : 0 < (i : ℕ) := by
        by_contra hnot
        have hi0 : (i : ℕ) = 0 := Nat.eq_zero_of_not_pos hnot
        have hcardpos : 0 < C.counts 0 := by
          rw [CombClass.counts]
          exact Fintype.card_pos_iff.mpr ⟨by simpa [hi0] using a⟩
        rw [hC] at hcardpos
        omega
      have htail : k ≤ n - (i : ℕ) := ih tail
      omega

private noncomputable def lpowIndexBoundEquiv (C : CombClass) (hC : C.counts 0 = 0)
    {m N : ℕ} (hmN : m ≤ N) :
    (Σ k : Fin (N + 1), (C.lpow (k : ℕ)).Obj m) ≃
      (Σ k : Fin (m + 1), (C.lpow (k : ℕ)).Obj m) where
  toFun x := by
    rcases x with ⟨k, obj⟩
    exact ⟨⟨(k : ℕ), Nat.lt_succ_of_le (lpow_length_le_size_of_obj C hC obj)⟩, obj⟩
  invFun x := by
    rcases x with ⟨k, obj⟩
    exact ⟨⟨(k : ℕ), Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ k.isLt) hmN)⟩, obj⟩
  left_inv x := by
    rcases x with ⟨k, obj⟩
    cases k
    rfl
  right_inv x := by
    rcases x with ⟨k, obj⟩
    cases k
    rfl

private abbrev LcycMid (C : CombClass) (n : ℕ) :=
  Σ S : Finset (Fin n), C.Obj (S.card + 1) × C.lseq.Obj (n - S.card)

private noncomputable def lengthSwapEquiv (C : CombClass) (hC : C.counts 0 = 0) (n : ℕ) :
    (Σ k : Fin (n + 1), RootedSmallData C n (k : ℕ)) ≃ LcycMid C n where
  toFun x := by
    rcases x with ⟨k, S, root, tail⟩
    have hmN : n - S.card ≤ n := Nat.sub_le n S.card
    exact ⟨S, root, lpowIndexBoundEquiv C hC hmN ⟨k, tail⟩⟩
  invFun x := by
    rcases x with ⟨S, root, seqTail⟩
    have hmN : n - S.card ≤ n := Nat.sub_le n S.card
    let p := (lpowIndexBoundEquiv C hC hmN).symm seqTail
    exact ⟨p.1, S, root, p.2⟩
  left_inv x := by
    rcases x with ⟨k, S, root, tail⟩
    dsimp
    have hmN : n - S.card ≤ n := Nat.sub_le n S.card
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    rcases x with ⟨S, root, seqTail⟩
    dsimp
    have hmN : n - S.card ≤ n := Nat.sub_le n S.card
    rw [Equiv.apply_symm_apply]

private noncomputable def lcycSourceMidEquiv (C : CombClass) (hC : C.counts 0 = 0)
    (n : ℕ) :
    C.lcyc.deriv.Obj n ≃ LcycMid C n :=
  (Equiv.sigmaCongrRight fun k : Fin (n + 1) =>
    (lpowSuccRootEquiv C n (k : ℕ)).trans (rootBlockDataEquiv C n (k : ℕ))).trans
      (lengthSwapEquiv C hC n)

/-- Pointing a canonical labelled cycle gives a distinguished `C`-block followed
by an arbitrary labelled sequence. -/
noncomputable def lcycDerivEquivLprodLseq (C : CombClass) (hC : C.counts 0 = 0)
    (n : ℕ) :
    C.lcyc.deriv.Obj n ≃ (C.deriv.lprod C.lseq).Obj n :=
  (lcycSourceMidEquiv C hC n).trans (lprodObjEquivBySubset C.deriv C.lseq n).symm

end AnalyticCombinatorics.Ch1


