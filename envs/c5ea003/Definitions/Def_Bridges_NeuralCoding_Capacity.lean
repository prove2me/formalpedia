-- Prove2me | Definitions.Def_Bridges_NeuralCoding_Capacity
-- name    : Bridges_NeuralCoding_Capacity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:54.159348+00:00
-- url     : https://prove2.me/theorems/c1c032c5-2cb9-4a93-afa6-9a9a3e26f09d
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_Capacity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.Capacity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/Capacity.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Neural Code Classification Capacity

## Overview

This file establishes the **founding theorem of tropical neural coding theory**:
for a finite neural code represented by tropical firing vectors, the tropical
convex hull geometry of each stimulus class controls certified separability,
explicit lower bounds on classification margins, and finiteness of the induced
classification quotient.

The conceptual leap: **classification capacity is read off from the arrangement
of tropical hulls of receptive-field codewords**. This turns neural coding into
a tropical-geometric theory of distinguishability.

## Main Definitions

* `classCode` — the subset of codewords assigned to a given stimulus class
* `realizableLabels` — the set of stimulus labels that appear in the code
* `classificationCapacity` — the number of distinct realizable stimulus classes
* `tropicalClassMargin` — certified tropical separation between two class hulls
* `globalTropicalMargin` — minimum pairwise tropical margin over all class pairs

## Main Results

* `classificationCapacity_le_code_size` — capacity is bounded by code size
* `realizableLabels_card_le` — number of realizable labels ≤ number of codewords
* `pairwise_positive_tropical_margin_implies_disjoint` — positive pairwise margins
  imply all class codes are disjoint
* `tropical_hull_determines_classification_capacity` — the headline theorem:
  positive pairwise margins yield finite capacity bounded by code size, with
  each realizable class having a nonempty code
* `positive_global_tropical_margin_yields_certified_multiclass_code` —
  a single positive global margin suffices for the full capacity bound
* `tropical_capacity_quotient_finite` — the label-induced quotient on codewords
  is finite, connecting to the neural quotient framework

## Cross-Domain Connections

- **Information theory**: `classificationCapacity` is the zero-error
  distinguishability count — a tropical analogue of channel capacity.
- **Quantum information**: parallels `superdense_coding_capacity` where
  geometric/physical structure amplifies distinguishability.
- **Operadic learning**: connects to
  `finite_neural_quotient_implies_finite_classification_quotient` via
  the classification quotient finiteness theorem.

## Keywords

tropical neural coding, certified multiclass classification, zero-error capacity,
receptive field geometry, neural code quotient, tropical information theory,
combinatorial classification capacity, margin certification, finite stimulus
distinguishability, tropical decision regions, geometric coding theory
-/

noncomputable section

open scoped Classical

open Finset BigOperators

/-! ## Core Definitions -/

/-- The **class code**: the subset of codewords in `X` assigned to stimulus class `k`
by the labeling function. This is the tropical firing pattern set for stimulus `k`. -/
def classCode {ι κ : Type*} [DecidableEq κ]
    (X : Finset (ι → ℝ)) (label : (ι → ℝ) → κ) (k : κ) : Finset (ι → ℝ) :=
  X.filter (fun x => label x = k)

/-- The **realizable labels**: stimulus classes that actually appear in the code.
These are the labels `k` for which at least one codeword in `X` maps to `k`. -/
def realizableLabels {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : Finset (ι → ℝ)) (label : (ι → ℝ) → κ) : Finset κ :=
  Finset.univ.filter (fun k => ∃ x ∈ X, label x = k)

/-- The **classification capacity**: the number of distinct stimulus classes
that are realized by the neural code. This is the tropical analogue of
zero-error channel capacity. -/
def classificationCapacity {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : Finset (ι → ℝ)) (label : (ι → ℝ) → κ) : ℕ :=
  (realizableLabels X label).card

/-- The **tropical class margin** between two class codes: the infimum over all
pairs `(a, b)` with `a ∈ A, b ∈ B` of the supremum coordinate gap `a i - b i`.
Positive margin certifies that the two classes are tropically separated.

In neural coding terms: this measures the minimum worst-case coordinate
separation between any pair of firing patterns from distinct stimulus classes. -/
def tropicalClassMargin {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : Finset (ι → ℝ)) : ℝ :=
  if hA : A.Nonempty then
    if hB : B.Nonempty then
      A.inf' hA (fun a => B.inf' hB (fun b =>
        Finset.sup' Finset.univ ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
          (fun i => a i - b i)))
    else 0
  else 0

/-- The **global tropical margin**: the minimum pairwise tropical class margin
over all distinct pairs of realizable stimulus classes. Positive global margin
certifies that the entire multiclass code is tropically separated.

This is the tropical analogue of minimum distance in coding theory. -/
def globalTropicalMargin {ι κ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ]
    (X : Finset (ι → ℝ)) (label : (ι → ℝ) → κ) : ℝ :=
  let pairs := (realizableLabels X label).product (realizableLabels X label)
      |>.filter (fun p => p.1 ≠ p.2)
  if h : pairs.Nonempty then
    pairs.inf' h (fun p => tropicalClassMargin (classCode X label p.1) (classCode X label p.2))
  else 0

/-! ## Basic Lemmas -/





/-
Positive pairwise tropical margin implies the class codes are pairwise
disjoint: no codeword can belong to two distinct stimulus classes.

In neural coding terms: if the tropical hulls of distinct stimulus classes
are separated by positive margin, then no single firing pattern can be
ambiguously assigned to multiple stimuli.
-/

/-! ## Capacity Theorems -/

/-
Each realizable label can be witnessed by a codeword, giving an injection
from realizable labels into `X`. Hence the number of realizable labels is
at most the number of codewords.
-/


/-
The classification capacity is at most the number of labels (trivially).
-/

/-
**Quotient Finiteness Theorem.**
The label-induced equivalence relation on codewords yields a finite quotient.
This connects to `finite_neural_quotient_implies_finite_classification_quotient`.
-/

/-
The classification capacity equals the cardinality of the realizable
label subtype.
-/

/-! ## Headline Theorems -/

/-
**Headline Theorem: Tropical Hull Determines Classification Capacity.**

For a finite neural code `X` with labeling function `label`, if every pair
of distinct stimulus classes has positive tropical class margin, then:
1. The classification capacity is well-defined and finite,
2. The capacity is bounded by the code size `|X|`,
3. Every realizable stimulus class has a nonempty class code.

This establishes that the **arrangement of tropical hulls of receptive-field
codewords** is a complete enough invariant for certified classification
capacity bounds in a finite setting.
-/

/-
**Global Margin Theorem.**
A single positive global tropical margin suffices for the full capacity bound.
-/

end


