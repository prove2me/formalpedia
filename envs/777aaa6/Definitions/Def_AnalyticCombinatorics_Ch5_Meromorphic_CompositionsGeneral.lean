-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch5_Meromorphic_CompositionsGeneral
-- name    : AnalyticCombinatorics_Ch5_Meromorphic_CompositionsGeneral
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:33:15.570252+00:00
-- url     : https://prove2.me/theorems/c685aa04-c2ba-47b5-9493-4c9f902a10f3
-- title:
--   Ordered compositions from a finite positive part set
-- statement:
--   For a finite set S of natural sizes, partPoly is the sum of x^s over S, and CompList S n is the type of ordered lists with entries in S and total sum n. BoundedSList stores lists over S of length at most n; it does not impose a total-sum condition. Excluding zero from S makes CompList finite and defines its cardinality compS and coefficient series compSeries. compOGF is the formal inverse of 1 minus the part series. The first-part equivalence splits a list of total n+1 into an allowed first part at most n+1 and a tail of the remaining total; this equivalence itself does not require zero exclusion. For at least two allowed sizes and zero excluded, rhoS selects a root of partPoly=1 in (0,1), with its existence proof included. The derivative sum defines residueConstant=1/P′(rho) and compAsymptoticConstant=1/(rho P′(rho)).
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/CompositionsGeneral.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# General finite-part-set compositions

This file develops the finite-alphabet composition model
`1 / (1 - ∑ s ∈ S, z^s)` for a finite nonempty set of positive parts.
-/

open Complex Filter Asymptotics
open scoped BigOperators ComplexOrder ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace CompositionsGeneral

/-- The part polynomial `P_S(x) = ∑_{s∈S} x^s` over a semiring. -/
def partPoly (R : Type*) [Semiring R] (S : Finset ℕ) (x : R) : R :=
  ∑ s ∈ S, x ^ s

/-- Genuine lists of natural-number parts from `S` summing to `n`. -/
def CompList (S : Finset ℕ) (n : ℕ) : Type :=
  {l : List ℕ // (∀ x ∈ l, x ∈ S) ∧ l.sum = n}

/-- Bounded lists over the finite alphabet `S`, used only to build the finite instance for
`CompList`.  The length bound follows from positivity of parts. -/
def BoundedSList (S : Finset ℕ) (n : ℕ) : Type :=
  Σ k : Fin (n + 1), List.Vector {x : ℕ // x ∈ S} k

namespace CompList

variable {S : Finset ℕ} {n : ℕ}

private def toBounded (h0 : 0 ∉ S) (l : CompList S n) : BoundedSList S n := by
  let lS : List {x : ℕ // x ∈ S} :=
    l.1.pmap (fun x hx => ⟨x, l.2.1 x hx⟩) (fun _ hx => hx)
  have hsum : (lS.map (fun x : {x : ℕ // x ∈ S} => x.1)).sum = n := by
    simpa [lS] using l.2.2
  have hpos : ∀ x ∈ l.1, 1 ≤ x := by
    intro x hx
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun hx0 => h0 (by simpa [hx0] using l.2.1 x hx))
  have hlen : l.1.length ≤ n := by
    exact (List.length_le_sum_of_one_le l.1 hpos).trans_eq l.2.2
  refine ⟨⟨l.1.length, Nat.lt_succ_of_le hlen⟩, ⟨lS, ?_⟩⟩
  simp [lS]

private def ofBounded (b : BoundedSList S n) : List ℕ :=
  b.2.1.map (fun x : {x : ℕ // x ∈ S} => x.1)

private lemma ofBounded_toBounded (h0 : 0 ∉ S) (l : CompList S n) :
    ofBounded (S := S) (n := n) (toBounded h0 l) = l.1 := by
  dsimp [ofBounded, toBounded]
  simp

private lemma toBounded_injective (h0 : 0 ∉ S) :
    Function.Injective (toBounded (S := S) (n := n) h0) := by
  intro l₁ l₂ h
  apply Subtype.ext
  have hvals := congrArg (ofBounded (S := S) (n := n)) h
  simpa [ofBounded_toBounded h0] using hvals

instance instFintypeBoundedSList (S : Finset ℕ) (n : ℕ) : Fintype (BoundedSList S n) := by
  classical
  letI : Fintype {x : ℕ // x ∈ S} := Finset.Subtype.fintype S
  exact inferInstanceAs (Fintype (Σ k : Fin (n + 1), List.Vector {x : ℕ // x ∈ S} (k : ℕ)))

instance instFintype (S : Finset ℕ) (n : ℕ) (h0 : 0 ∉ S) : Fintype (CompList S n) := by
  classical
  letI : Fintype (BoundedSList S n) := instFintypeBoundedSList S n
  exact Fintype.ofInjective (toBounded (S := S) (n := n) h0) (toBounded_injective h0)

end CompList

/-- Number of ordered compositions of `n` with parts in `S`. -/
def compS (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) : ℕ :=
  letI : Fintype (CompList S n) := CompList.instFintype S n h0
  Fintype.card (CompList S n)

/-- The formal OGF with genuine list-count coefficients. -/
def compSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (compS S h0 n : ℂ)

/-- The rational OGF `1 / (1 - ∑_{s∈S} z^s)`. -/
def compOGFℂ (S : Finset ℕ) : PowerSeries ℂ :=
  (1 - ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s)⁻¹

lemma partPoly_zero_of_notMem_zero {R : Type*} [Semiring R] (S : Finset ℕ) (h0 : 0 ∉ S) :
    partPoly R S 0 = 0 := by
  classical
  rw [partPoly]
  refine Finset.sum_eq_zero fun s hs => ?_
  have hs0 : s ≠ 0 := fun h => h0 (by simpa [h] using hs)
  simp [hs0]

lemma partPoly_one (S : Finset ℕ) :
    partPoly ℝ S 1 = (S.card : ℝ) := by
  simp [partPoly]

lemma partPoly_continuous (S : Finset ℕ) :
    Continuous (partPoly ℝ S) := by
  classical
  unfold partPoly
  fun_prop

lemma list_eq_nil_of_sum_eq_zero_of_one_le (l : List ℕ)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hsum : l.sum = 0) :
    l = [] := by
  cases l with
  | nil => rfl
  | cons x xs =>
      have hx : 1 ≤ x := hpos x (by simp)
      have h : x + xs.sum = 0 := by simpa using hsum
      omega

lemma compList_zero_eq_nil {S : Finset ℕ} (h0 : 0 ∉ S) (l : CompList S 0) :
    l.1 = [] := by
  apply list_eq_nil_of_sum_eq_zero_of_one_le l.1
  · intro x hx
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun hx0 => h0 (by simpa [hx0] using l.2.1 x hx))
  · exact l.2.2

def compListZeroEquivPUnit (S : Finset ℕ) (h0 : 0 ∉ S) :
    CompList S 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], by simp⟩
  left_inv l := by
    apply Subtype.ext
    exact (compList_zero_eq_nil h0 l).symm
  right_inv u := by
    cases u
    rfl

instance instFintypePartLe (S : Finset ℕ) (n : ℕ) :
    Fintype {s : ℕ // s ∈ S ∧ s ≤ n} := by
  classical
  letI : Fintype {s : ℕ // s ∈ S} := Finset.Subtype.fintype S
  exact Fintype.ofInjective
    (fun s : {s : ℕ // s ∈ S ∧ s ≤ n} => (⟨s.1, s.2.1⟩ : {s : ℕ // s ∈ S}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun t : {s : ℕ // s ∈ S} => t.1) h)

def firstPartCodomain (S : Finset ℕ) (n : ℕ) : Type :=
  Σ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1}, CompList S (n + 1 - s.1)

private def firstPart (S : Finset ℕ) (n : ℕ) :
    CompList S (n + 1) → firstPartCodomain S n := by
  intro l
  cases l with
  | mk xs hxs =>
    cases xs with
    | nil =>
        have h : (0 : ℕ) = n + 1 := by simpa using hxs.2
        omega
    | cons x xs =>
        have hxS : x ∈ S := hxs.1 x (by simp)
        have hsum_cons : x + xs.sum = n + 1 := by
          simpa using hxs.2
        have hxle : x ≤ n + 1 := by omega
        refine ⟨⟨x, hxS, hxle⟩, ⟨xs, ?_, ?_⟩⟩
        · intro y hy
          exact hxs.1 y (by simp [hy])
        · show xs.sum = n + 1 - x
          omega

private def consPart (S : Finset ℕ) (n : ℕ) :
    firstPartCodomain S n → CompList S (n + 1) := by
  intro a
  rcases a with ⟨s, l⟩
  refine ⟨s.1 :: l.1, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · simpa [hx] using s.2.1
    · exact l.2.1 x hx
  · simp
    have hsle : s.1 ≤ n + 1 := s.2.2
    have hsum : l.1.sum = n + 1 - s.1 := l.2.2
    show s.1 + l.1.sum = n + 1
    omega

private lemma consPart_firstPart (S : Finset ℕ) (n : ℕ) (l : CompList S (n + 1)) :
    consPart S n (firstPart S n l) = l := by
  apply Subtype.ext
  cases l with
  | mk xs hxs =>
    cases xs with
    | nil =>
        have h : (0 : ℕ) = n + 1 := by simpa using hxs.2
        omega
    | cons x xs =>
        rfl

private lemma firstPart_consPart (S : Finset ℕ) (n : ℕ) (a : firstPartCodomain S n) :
    firstPart S n (consPart S n a) = a := by
  rcases a with ⟨⟨x, hxS, hxle⟩, ⟨xs, hmem, hsum⟩⟩
  apply Sigma.ext
  · apply Subtype.ext
    rfl
  · simp [firstPart, consPart]

def compListSuccEquivSigma (S : Finset ℕ) (n : ℕ) :
    CompList S (n + 1) ≃ firstPartCodomain S n where
  toFun := firstPart S n
  invFun := consPart S n
  left_inv := consPart_firstPart S n
  right_inv := firstPart_consPart S n

lemma exists_partPoly_eq_one {S : Finset ℕ} (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ partPoly ℝ S ρ = 1 := by
  classical
  have h0le1 : (0 : ℝ) ≤ 1 := by norm_num
  have hcont : ContinuousOn (partPoly ℝ S) (Set.Icc 0 1) :=
    (partPoly_continuous S).continuousOn
  have hP0 : partPoly ℝ S 0 = 0 :=
    partPoly_zero_of_notMem_zero (R := ℝ) S h0
  have hP1 : partPoly ℝ S 1 = (S.card : ℝ) :=
    partPoly_one S
  have hP0P1 : partPoly ℝ S 0 ≤ partPoly ℝ S 1 := by
    rw [hP0, hP1]
    exact_mod_cast Nat.zero_le S.card
  have hmem : (1 : ℝ) ∈ Set.Icc (partPoly ℝ S 0) (partPoly ℝ S 1) := by
    rw [partPoly_one]
    rw [hP0]
    constructor
    · norm_num
    · have hcardReal : (1 : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hcard)
      simpa using hcardReal
  rcases intermediate_value_Icc h0le1 hcont hmem with ⟨ρ, hρIcc, hρ⟩
  refine ⟨ρ, ?_, ?_, hρ⟩
  · by_contra hnot
    have hρ0 : ρ = 0 := le_antisymm (not_lt.mp hnot) hρIcc.1
    have hzero : partPoly ℝ S ρ = 0 := by
      rw [hρ0]
      exact partPoly_zero_of_notMem_zero (R := ℝ) S h0
    linarith
  · by_contra hnot
    have hρ1 : ρ = 1 := le_antisymm hρIcc.2 (not_lt.mp hnot)
    have hone : partPoly ℝ S ρ = (S.card : ℝ) := by
      rw [hρ1, partPoly_one]
    have hcardReal : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
    linarith

/-- The positive root as an arbitrary witness.  Theorems below expose its properties. -/
def rhoS (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) : ℝ :=
  Classical.choose (exists_partPoly_eq_one (S := S) hcard h0)

/-- Formal derivative of the part polynomial at a complex point. -/
def partPolyDerivAt (S : Finset ℕ) (ρ : ℂ) : ℂ :=
  ∑ s ∈ S, (s : ℂ) * ρ ^ (s - 1)

/-- The dominant pole as a complex number. -/
def rhoSℂ (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) : ℂ :=
  (rhoS S hcard h0 : ℂ)

/-- The `c = 1 / P_S'(ρ)` principal-part constant. -/
def residueConstant (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) : ℂ :=
  (partPolyDerivAt S (rhoSℂ S hcard h0))⁻¹

/-- Coefficient asymptotic constant, equal to `1 / (ρ P_S'(ρ))`. -/
def compAsymptoticConstant (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) : ℂ :=
  residueConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹

end CompositionsGeneral
end Meromorphic
end Ch5
end AnalyticCombinatorics


