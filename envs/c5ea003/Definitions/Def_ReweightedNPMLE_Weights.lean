-- Prove2me | Definitions.Def_ReweightedNPMLE_Weights
-- name    : ReweightedNPMLE_Weights
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:14:23.534239+00:00
-- url     : https://prove2.me/theorems/96fbe76d-10e8-4c4f-827f-3c4c16cbe71b
-- title:
--   Weighted log likelihood and fitted-value maximizers
-- statement:
--   For finite vectors \(w,v\in\mathbb R^n\), define the total weight and weighted log likelihood by
--   \[
--   T(w)=\sum_{i=1}^n w_i,\qquad
--   \ell_w(v)=\sum_{i=1}^n w_i\log v_i.
--   \]
--   The positive fitted-value domain is \(\mathbb R_{++}^n=\{v:v_i>0\ \forall i\}\). The predicate that \(v\) maximizes a function \(f\) over \(C\) means both \(v\in C\) and \(f(u)\le f(v)\) for every \(u\in C\). The positive orthant is convex, and \(\ell_w\) is continuous there for every real weight vector. Consequently every nonempty compact subset of the positive orthant admits a maximizer, including when some weights are zero or negative.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Weights.lean#L18-L108

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact

/-!
# Weighted likelihood and normalization

This file formalizes the deterministic normalization statements in Section 2.2 of the
paper.  Vectors are represented by functions on `Fin n`; this is the representation used
throughout the rest of the development.
-/

open scoped BigOperators

namespace ReweightedNPMLE

/-- The sum of the coordinates of a finite real vector. -/
def total {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, w i



/-- The finite weighted log-likelihood of a positive fitted-value vector. -/
noncomputable def weightedLogLikelihood {n : ℕ} (w v : Fin n → ℝ) : ℝ :=
  ∑ i, w i * Real.log (v i)

/-- A point `v` maximizes `f` on the feasible set `C`. -/
def IsMaxOn {E : Type*} (C : Set E) (f : E → ℝ) (v : E) : Prop :=
  v ∈ C ∧ ∀ u ∈ C, f u ≤ f v

/-- The strictly positive orthant containing all fitted-value vectors. -/
def positiveVectors (n : ℕ) : Set (Fin n → ℝ) :=
  {v | ∀ i, 0 < v i}

theorem convex_positiveVectors (n : ℕ) : Convex ℝ (positiveVectors n) := by
  intro x hx y hy a b ha hb hab i
  change 0 < a * x i + b * y i
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_mul, zero_add] at hab ⊢
    subst b
    simpa using hy i
  · rcases hb.eq_or_lt with rfl | hb
    · simp only [mul_zero, add_zero] at hab ⊢
      subst a
      simpa using hx i
    · exact add_pos (mul_pos ha (hx i)) (mul_pos hb (hy i))



/-- The finite weighted log-likelihood is continuous on the positive orthant. -/
theorem continuousOn_weightedLogLikelihood {n : ℕ} (w : Fin n → ℝ) :
    ContinuousOn (weightedLogLikelihood w) (positiveVectors n) := by
  change ContinuousOn (fun v ↦ ∑ i : Fin n, w i * Real.log (v i)) (positiveVectors n)
  apply continuousOn_finsetSum Finset.univ
  intro i _ v hv
  have happ : ContinuousAt (fun z : Fin n → ℝ ↦ z i) v :=
    (continuous_apply i).continuousAt
  exact ((Real.continuousAt_log (hv i).ne').comp
    (f := fun z : Fin n → ℝ ↦ z i) (x := v) happ).const_mul (w i) |>.continuousWithinAt

/-- A nonempty compact positive fitted-value set has a weighted maximizer. -/
theorem exists_fittedValue_maximizer {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) :
    ∃ v, IsMaxOn C (weightedLogLikelihood w) v := by
  obtain ⟨v, hvC, hvmax⟩ := hCcompact.exists_isMaxOn hCnonempty
    ((continuousOn_weightedLogLikelihood w).mono hCpos)
  exact ⟨v, hvC, fun u hu ↦ hvmax hu⟩



























end ReweightedNPMLE


