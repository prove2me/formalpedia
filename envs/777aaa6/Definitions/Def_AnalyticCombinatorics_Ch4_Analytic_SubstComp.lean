-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
-- name    : AnalyticCombinatorics_Ch4_Analytic_SubstComp
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:32:25.040787+00:00
-- url     : https://prove2.me/theorems/3cfd96a9-367b-43db-b965-ddf8dff39a68
-- title:
--   Finite indexing equivalences supporting substitution of power series
-- statement:
--   Four finite indexing equivalences support substitution of formal power series. Finitely supported antidiagonal indices on range g with sum m correspond to nonnegative tuples indexed by Fin g with sum m. Positive tuples indexed by Fin d with sum n correspond to ordered compositions of n of length d. A further equivalence rearranges the positivity and sum constraints, and the disjoint union over lengths d less than n+1 recovers all compositions of n. The complete forward maps, inverse maps and inverse proofs are included; zero-length and zero-total cases are retained.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/SubstComp.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


open scoped BigOperators PowerSeries
open List Finset

noncomputable section

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

noncomputable def positiveFinTupleCompositionEquiv (n d : ℕ) :
    { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n } ≃
      { c : Composition n // c.length = d } where
  toFun l := by
    refine ⟨{ blocks := List.ofFn l.1, blocks_pos := ?_, blocks_sum := ?_ }, ?_⟩
    · intro x hx
      rw [List.mem_ofFn'] at hx
      rcases hx with ⟨i, rfl⟩
      exact l.2.1 i
    · simpa [List.sum_ofFn] using l.2.2
    · simp [Composition.length]
  invFun c := by
    refine ⟨fun i : Fin d => c.1.blocksFun ((finCongr c.2.symm) i), ?_⟩
    constructor
    · intro i
      exact c.1.one_le_blocksFun ((finCongr c.2.symm) i)
    · calc
        (∑ i : Fin d, c.1.blocksFun ((finCongr c.2.symm) i)) =
            ∑ j : Fin c.1.length, c.1.blocksFun j := by
          exact Fintype.sum_equiv (finCongr c.2.symm)
            (fun i : Fin d => c.1.blocksFun ((finCongr c.2.symm) i))
            (fun j : Fin c.1.length => c.1.blocksFun j) (by intro i; rfl)
        _ = n := c.1.sum_blocksFun
  left_inv l := by
    apply Subtype.ext
    funext i
    simp [Composition.blocksFun]
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    ext1
    change List.ofFn (fun i : Fin d => c.blocksFun ((finCongr hc.symm) i)) = c.blocks
    subst d
    simp [Composition.ofFn_blocksFun]

noncomputable def positiveSubtypeEquiv (n d : ℕ) :
    { x : { y : Fin d → ℕ // ∑ i, y i = n } // ∀ i, 0 < x.1 i } ≃
      { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n } where
  toFun x := ⟨x.1.1, x.2, x.1.2⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv x := by rfl
  right_inv x := by rfl

noncomputable def sigmaLengthCompositionEquiv (n : ℕ) :
    (Sigma fun d : Fin (n + 1) => { c : Composition n // c.length = d.val }) ≃
      Composition n where
  toFun x := x.2.1
  invFun c := ⟨⟨c.length, Nat.lt_succ_of_le c.length_le⟩, ⟨c, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨⟨d, _hd⟩, c, hc⟩
    dsimp at hc
    subst d
    simp
  right_inv c := by rfl


