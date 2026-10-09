-- Prove2me | Definitions.Def_Nonadditivity_StateEnsembles
-- name    : Nonadditivity_StateEnsembles
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:23:29.053988+00:00
-- url     : https://prove2.me/theorems/a5204f29-74d6-45f7-bb56-1fea38e8de0e
-- title:
--   Finite state ensembles and their Holevo information
-- statement:
--   A finite ensemble consists of density matrices with nonnegative weights summing to one. Its average state is their weighted mixture, and its Holevo information is the entropy of the average minus the weighted average of the individual entropies. The interface defines the supremum of this information over ensembles in a given set of states and the associated minimum entropy. It proves boundedness, the entropy upper estimate for the supremum, and an orbit lower estimate when an ensemble averages to the maximally mixed state. Entropies use natural logarithms.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/StateEnsembles.lean#L25-L197

import Definitions.Def_Nonadditivity_Entropy
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-!
# Ensembles of actual quantum states

Every average below is proved positive semidefinite and trace one. The
Holevo quantity is a supremum over normalized finite ensembles of states in
the specified output set. Entropies use natural logarithms.
-/

noncomputable section

namespace Nonadditivity.Entropy

open scoped BigOperators ComplexOrder Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[ext] theorem DensityMatrix.ext {ρ σ : DensityMatrix ι}
    (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- A convex combination is an actual state, including zero-weight terms. -/
def DensityMatrix.mixture {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1)
    (ρ : κ → DensityMatrix ι) : DensityMatrix ι where
  matrix := ∑ k, (p k : ℂ) • (ρ k).matrix
  positive := Matrix.posSemidef_sum _ (fun k _ => (ρ k).positive.smul
    (show (0 : ℂ) ≤ (p k : ℂ) by exact_mod_cast hp k))
  normalized := by
    simp only [Matrix.trace_sum, Matrix.trace_smul, DensityMatrix.normalized]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hsum]
    simp

@[simp] theorem DensityMatrix.mixture_matrix {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1)
    (ρ : κ → DensityMatrix ι) :
    (DensityMatrix.mixture p hp hsum ρ).matrix = ∑ k, (p k : ℂ) • (ρ k).matrix := rfl

/-- The completely mixed state. -/
def maximallyMixed (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    DensityMatrix ι where
  matrix := ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)
  positive := Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) by
    exact_mod_cast (show (0 : ℝ) ≤ 1 / (Fintype.card ι : ℝ) by positivity))
  normalized := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    simp only [smul_eq_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast]
    field_simp

theorem maximallyMixed_purity [Nonempty ι] :
    (maximallyMixed ι).purity = 1 / (Fintype.card ι : ℝ) := by
  have h := (maximallyMixed ι).trace_square_eq_purity
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : ((maximallyMixed ι).matrix * (maximallyMixed ι).matrix).trace =
      ((1 / (Fintype.card ι : ℝ) : ℝ) : ℂ) := by
    simp only [maximallyMixed, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.trace_smul, Matrix.trace_one, smul_smul]
    simp only [smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_natCast]
    congr 1
    field_simp
  rw [hm] at h
  exact Complex.ofReal_injective h.symm

theorem maximallyMixed_entropy [Nonempty ι] :
    (maximallyMixed ι).vonNeumann = Real.log (Fintype.card ι) := by
  apply le_antisymm (maximallyMixed ι).vonNeumann_le_log_dim
  have h := (maximallyMixed ι).vonNeumann_ge_neg_log_purity
  simpa [maximallyMixed_purity, Real.log_inv] using h

end Nonadditivity.Entropy

namespace Nonadditivity.StateEnsembles

open Entropy
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Ensemble (outputs : Set (DensityMatrix ι)) where
  size : ℕ
  weight : Fin size → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  state : Fin size → DensityMatrix ι
  state_mem : ∀ i, state i ∈ outputs

def Ensemble.average {outputs : Set (DensityMatrix ι)} (e : Ensemble outputs) :
    DensityMatrix ι :=
  DensityMatrix.mixture e.weight e.weight_nonneg e.weight_sum e.state

def Ensemble.information {outputs : Set (DensityMatrix ι)} (e : Ensemble outputs) : ℝ :=
  e.average.vonNeumann - ∑ i, e.weight i * (e.state i).vonNeumann

def minimumEntropy (outputs : Set (DensityMatrix ι)) : ℝ :=
  sInf (DensityMatrix.vonNeumann '' outputs)

def quantity (outputs : Set (DensityMatrix ι)) : ℝ :=
  sSup (Set.range fun e : Ensemble outputs => e.information)

def singleton {outputs : Set (DensityMatrix ι)} (ρ : DensityMatrix ι)
    (hρ : ρ ∈ outputs) : Ensemble outputs where
  size := 1
  weight := fun _ => 1
  weight_nonneg := fun _ => zero_le_one
  weight_sum := by simp
  state := fun _ => ρ
  state_mem := fun _ => hρ

@[simp] theorem singleton_information {outputs : Set (DensityMatrix ι)}
    (ρ : DensityMatrix ι) (hρ : ρ ∈ outputs) :
    (singleton ρ hρ).information = 0 := by
  have ha : (singleton ρ hρ).average = ρ := by
    apply DensityMatrix.ext
    simp [Ensemble.average, singleton]
  unfold Ensemble.information
  rw [ha]
  simp [singleton]

theorem entropy_bddBelow (outputs : Set (DensityMatrix ι)) :
    BddBelow (DensityMatrix.vonNeumann '' outputs) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨ρ, _, rfl⟩
  exact ρ.vonNeumann_nonneg

theorem minimumEntropy_le {outputs : Set (DensityMatrix ι)}
    {ρ : DensityMatrix ι} (hρ : ρ ∈ outputs) :
    minimumEntropy outputs ≤ ρ.vonNeumann :=
  csInf_le (entropy_bddBelow outputs) ⟨ρ, hρ, rfl⟩

theorem information_le [Nonempty ι] {outputs : Set (DensityMatrix ι)}
    (e : Ensemble outputs) {s : ℝ}
    (hmin : ∀ ρ ∈ outputs, s ≤ ρ.vonNeumann) :
    e.information ≤ Real.log (Fintype.card ι) - s := by
  have hsum : s ≤ ∑ i, e.weight i * (e.state i).vonNeumann := by
    calc
      s = ∑ i, e.weight i * s := by rw [← Finset.sum_mul, e.weight_sum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hmin _ (e.state_mem i)) (e.weight_nonneg i)
  have hmax := e.average.vonNeumann_le_log_dim
  unfold Ensemble.information
  linarith

theorem information_bddAbove [Nonempty ι] (outputs : Set (DensityMatrix ι)) :
    BddAbove (Set.range fun e : Ensemble outputs => e.information) := by
  refine ⟨Real.log (Fintype.card ι), ?_⟩
  rintro _ ⟨e, rfl⟩
  simpa using information_le e (fun ρ _ => ρ.vonNeumann_nonneg)



/-- The upper Holevo bound for a set of genuine quantum outputs. -/
theorem quantity_le [Nonempty ι] {outputs : Set (DensityMatrix ι)}
    (hne : outputs.Nonempty) {s : ℝ}
    (hmin : ∀ ρ ∈ outputs, s ≤ ρ.vonNeumann) :
    quantity outputs ≤ Real.log (Fintype.card ι) - s := by
  obtain ⟨ρ, hρ⟩ := hne
  unfold quantity
  have hs : (Set.range fun e : Ensemble outputs => e.information).Nonempty :=
    ⟨(singleton ρ hρ).information, singleton ρ hρ, rfl⟩
  apply csSup_le hs
  rintro _ ⟨e, rfl⟩
  exact information_le e hmin



/-- An orbit of *any* output gives a lower bound, without a minimizing state. -/
theorem orbit_lower_bound [Nonempty ι] {outputs : Set (DensityMatrix ι)}
    (e : Ensemble outputs) (ρ : DensityMatrix ι)
    (havg : e.average = maximallyMixed ι)
    (hent : ∀ i, (e.state i).vonNeumann = ρ.vonNeumann) :
    Real.log (Fintype.card ι) - ρ.vonNeumann ≤ quantity outputs := by
  have hinfo : e.information = Real.log (Fintype.card ι) - ρ.vonNeumann := by
    unfold Ensemble.information
    simp_rw [hent]
    rw [← Finset.sum_mul, e.weight_sum, one_mul, havg, maximallyMixed_entropy]
  rw [← hinfo]
  exact le_csSup (information_bddAbove outputs) ⟨e, rfl⟩



end Nonadditivity.StateEnsembles


