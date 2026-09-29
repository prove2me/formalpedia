-- Prove2me | Definitions.Def_Novelty_ConsciousnessIntegratedInformationConnector
-- name    : Novelty_ConsciousnessIntegratedInformationConnector
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:10:00.681246+00:00
-- url     : https://prove2.me/theorems/37254a3e-b668-43ef-8463-979dacbe2c00
-- title:
--   Aether Catalog definitions — Novelty_ConsciousnessIntegratedInformationConnector
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ConsciousnessIntegratedInformationConnector`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ConsciousnessIntegratedInformationConnector.lean by skeleton subtraction
import Mathlib

/-! # Integrated information as weighted graph connectivity

This self-contained development formalizes a finite-cut core of Integrated
Information Theory (IIT) and proves a cross-domain bridge to weighted graph
connectivity.  Effective information is minimized over nontrivial cuts.  When
effective information is the total interaction weight crossing a cut, strictly
positive integrated information is equivalent to the graph-theoretic condition
that every nontrivial cut carries a positive interaction.
-/

open Finset

namespace IntegratedInformationConnector

variable {n : ℕ}

/-- Nonempty proper subsets, representing nontrivial bipartitions. -/
def parts (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset.filter (fun A => A.Nonempty ∧ A ≠ univ)


/-- There is a nontrivial bipartition when there are at least two elements. -/
theorem parts_nonempty (h : 2 ≤ n) : (parts n).Nonempty := by
  simp +decide [parts]
  refine' ⟨{⟨0, by omega⟩}, _⟩
  simp +decide
  exact ne_of_apply_ne Finset.card (by simp +decide [Finset.card_univ]; omega)

/-- A finite system together with its nonnegative effective-information value
on each candidate cut. -/
structure System (n : ℕ) where
  ei : Finset (Fin n) → ℝ
  ei_nonneg : ∀ A, 0 ≤ ei A

/-- Integrated information `Φ`, the minimum effective information among all
nontrivial bipartitions. -/
noncomputable def Phi (S : System n) (h : 2 ≤ n) : ℝ :=
  ((parts n).image S.ei).min' ((parts_nonempty h).image S.ei)





/-- Total directed interaction weight crossing from `A` to its complement. -/
def cutWeight (w : Fin n → Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ Aᶜ, w i j

/-- Every nontrivial cut has positive crossing interaction.  This is the cut
form of connectivity for the positive-weight directed interaction network. -/
def CutConnected (w : Fin n → Fin n → ℝ) : Prop :=
  ∀ A ∈ parts n, 0 < cutWeight w A

/-- A nonnegative weighted network as an IIT system. -/
def weightedCutSystem (w : Fin n → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) : System n where
  ei := cutWeight w
  ei_nonneg A := by
    simp only [cutWeight]
    exact sum_nonneg fun i _ => sum_nonneg fun j _ => hw i j



end IntegratedInformationConnector


