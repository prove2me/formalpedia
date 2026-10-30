-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_CycleOGF
-- name    : AnalyticCombinatorics_Ch1_OGF_CycleOGF
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:20:01.72175+00:00
-- url     : https://prove2.me/theorems/40676c18-cb6a-4d2b-98c6-72b62707292c
-- title:
--   Cycle classes and coefficientwise logarithmic series
-- statement:
--   A size-n cycle consists of a length-k rotation necklace for some 1≤k≤n. The formal series mlog(f)=Σ_{j≥1}f^j/j and the totient-weighted sum Σ_{d≥1}φ(d)mlog(A(z^d))/d encode its coefficients. Finite equivalences distribute component sizes among word positions. Rational coefficients carry the discrete topology and power series the coefficientwise topology.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/CycleOGF.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_CycleModel
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.Rat
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
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.2 — The cycle construction OGF layer

This file connects the Burnside count for cycle necklaces to the ordinary
generating function identity

  `CYC(C)(z) = ∑_{d ≥ 1} φ(d)/d * mlog(C(z^d))`.
-/

namespace AnalyticCombinatorics.Ch1

open scoped BigOperators PowerSeries.WithPiTopology
open PowerSeries
open PowerSeries.WithPiTopology

local instance instTopRatCycleOGF : TopologicalSpace ℚ := ⊥

noncomputable def blockWordSigmaEquiv
    (C : CombClass) (m g : ℕ) :
    BlockWord C m g ≃
      Σ l : { l : Fin g → ℕ // ∑ i, l i = m }, ∀ i, C.Obj (l.1 i) where
  toFun w :=
    ⟨⟨fun i => compSize (w.1 i), w.2⟩, fun i => (w.1 i).2⟩
  invFun x := by
    classical
    refine ⟨fun i => ⟨⟨x.1.1 i, Nat.lt_succ_of_le ?_⟩, x.2 i⟩, ?_⟩
    · exact (le_sum_univ_nat x.1.1 i).trans (le_of_eq x.1.2)
    · exact x.1.2
  left_inv w := by
    apply Subtype.ext
    funext i
    cases hcomp : w.1 i with
    | mk s obj =>
        simp [compSize, hcomp]
  right_inv x := by
    cases x with
    | mk l objs =>
        apply Sigma.ext
        · apply Subtype.ext
          funext i
          rfl
        · exact HEq.rfl

noncomputable def finsuppAntidiagRangeEquivFin (m g : ℕ) :
    (Finset.range g).finsuppAntidiag m ≃
      { l : Fin g → ℕ // ∑ i, l i = m } where
  toFun l := by
    refine ⟨fun i => l.1 i.val, ?_⟩
    have hl := (Finset.mem_finsuppAntidiag.mp l.2).1
    calc
      (∑ i : Fin g, l.1 i.val) =
          ∑ i ∈ Finset.range g, if h : i < g then l.1 i else 0 :=
        Finset.sum_fin_eq_sum_range (fun i : Fin g => l.1 i.val)
      _ = ∑ i ∈ Finset.range g, l.1 i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [dif_pos (Finset.mem_range.mp hi)]
      _ = m := hl
  invFun l := by
    classical
    let f : ℕ → ℕ := fun i => if h : i < g then l.1 ⟨i, h⟩ else 0
    let fs : ℕ →₀ ℕ := Finsupp.onFinset (Finset.range g) f (by
      intro i hi
      by_cases h : i < g
      · exact Finset.mem_range.mpr h
      · simp [f, h] at hi)
    refine ⟨fs, ?_⟩
    rw [Finset.mem_finsuppAntidiag]
    constructor
    · change ∑ i ∈ Finset.range g, fs i = m
      have hsum : (∑ i : Fin g, fs i.val) = m := by
        simpa [fs, f] using l.2
      calc
        (∑ i ∈ Finset.range g, fs i) =
            ∑ i ∈ Finset.range g, if h : i < g then fs i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [dif_pos (Finset.mem_range.mp hi)]
        _ = ∑ i : Fin g, fs i.val :=
          (Finset.sum_fin_eq_sum_range (fun i : Fin g => fs i.val)).symm
        _ = m := hsum
    · intro i hi
      rw [Finsupp.mem_support_iff] at hi
      by_cases h : i < g
      · exact Finset.mem_range.mpr h
      · exfalso
        exact hi (by simp [fs, f, h])
  left_inv l := by
    apply Subtype.ext
    ext i
    by_cases h : i < g
    · simp [h]
    · have hsupp := (Finset.mem_finsuppAntidiag.mp l.2).2
      have hinotsupp : i ∉ l.1.support := by
        intro hi
        exact h (Finset.mem_range.mp (hsupp hi))
      have hzero : l.1 i = 0 := by
        simpa [Finsupp.mem_support_iff] using hinotsupp
      simp [h, hzero]
  right_inv l := by
    apply Subtype.ext
    funext i
    simp

noncomputable def mlog (f : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  ∑' j : ℕ, (((j + 1 : ℕ) : ℚ)⁻¹) • f ^ (j + 1)

noncomputable def CombClass.cyc (C : CombClass) : CombClass where
  Obj n := Σ k : (Finset.Icc 1 n),
    letI : NeZero k.1 :=
      ⟨Nat.ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp k.2).1)⟩
    necklaces_k C n k.1
  finObj _ := by
    classical
    infer_instance

noncomputable def cycRHS (C : CombClass) : ℚ⟦X⟧ :=
  ∑' d : ℕ,
    ((Nat.totient (d + 1) : ℚ) / ((d + 1 : ℕ) : ℚ)) •
      mlog (PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ (d + 1)) C.ogf)

end AnalyticCombinatorics.Ch1


