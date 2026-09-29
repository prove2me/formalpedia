-- Prove2me | Definitions.Def_Tropical_NeuralCoding_TropicalPruning
-- name    : Tropical_NeuralCoding_TropicalPruning
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:42:25.943995+00:00
-- url     : https://prove2.me/theorems/48a38d09-d806-4dcb-91fe-4b181c419e25
-- title:
--   Aether Catalog definitions — Tropical_NeuralCoding_TropicalPruning
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.NeuralCoding.TropicalPruning`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/NeuralCoding/TropicalPruning.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Polynomial Pruning: Certified Semantic Compression

This file establishes the mathematical foundations for **tropical polynomial pruning**,
a framework for certified compression and interpretability of piecewise-linear models
(such as ReLU neural networks) through tropical geometry.

## Overview

A tropical polynomial is a finite maximum of affine forms. Canonical pruning removes
monomials (affine templates) that are *strictly* dominated on a finite domain — meaning
there exists another monomial that is at least as large everywhere and strictly larger
somewhere. This yields an equivalent but potentially smaller tropical polynomial.

## Key Design Choice: Strict Domination

We use **strict domination** (≤ everywhere, < somewhere) rather than weak domination
(≤ everywhere). This is essential because weak domination can cause mutual elimination
of functionally equivalent but structurally distinct monomials, breaking the preservation
theorem. Strict domination is acyclic on finite sets, ensuring that the pruning process
terminates with correct semantics.

## Main Results

* `canonicalOn_eval_eq` — **Theorem A**: Canonical pruning preserves evaluation.
* `max_affine_relu_bridge` — Max of affine forms is ReLU-computable.
* `relu_tropical_pruning_sound` — **Theorem B**: ReLU-tropical pruning soundness.
* `card_canonicalOn_le` — **Theorem D**: Canonical support ≤ original support.
-/

noncomputable section

open Finset BigOperators

/-! ## Core Definitions -/

/-- A tropical monomial (affine template) in `n` variables.
    Represents `x ↦ bias + ∑ᵢ weight i * x i`. -/
structure TPMonomial (n : ℕ) where
  bias : ℝ
  weight : Fin n → ℝ
  deriving DecidableEq

namespace TPMonomial

/-- Evaluate a tropical monomial at a point. -/
def eval {n : ℕ} (m : TPMonomial n) (x : Fin n → ℝ) : ℝ :=
  m.bias + ∑ i, m.weight i * x i


end TPMonomial

/-- A tropical polynomial: a nonempty finite set of monomials.
    Evaluation takes the supremum (max). -/
structure TPoly (n : ℕ) where
  support : Finset (TPMonomial n)
  nonempty : support.Nonempty

namespace TPoly

/-- Evaluate: max over monomial evaluations. -/
def eval {n : ℕ} (p : TPoly n) (x : Fin n → ℝ) : ℝ :=
  p.support.sup' p.nonempty (fun m => m.eval x)


end TPoly

/-- **Strict domination**: `m` is strictly dominated by `m'` on domain `D` if
    `m.eval x ≤ m'.eval x` for all `x ∈ D`, and `m.eval x < m'.eval x` for
    some `x ∈ D`. This is acyclic on finite domains, which is essential for
    the pruning preservation theorem. -/
def StrictlyDominatedOn {n : ℕ} (D : Finset (Fin n → ℝ)) (m m' : TPMonomial n) : Prop :=
  (∀ x ∈ D, m.eval x ≤ m'.eval x) ∧ (∃ x ∈ D, m.eval x < m'.eval x)

/-- A monomial is strictly dominated in a polynomial if some other support monomial
    strictly dominates it on the entire domain. -/
def IsStrictlyDominated {n : ℕ} (D : Finset (Fin n → ℝ)) (p : TPoly n)
    (m : TPMonomial n) : Prop :=
  ∃ m' ∈ p.support, m' ≠ m ∧ StrictlyDominatedOn D m m'

instance instDecStrictlyDominatedOn {n : ℕ} (D : Finset (Fin n → ℝ))
    (m m' : TPMonomial n) : Decidable (StrictlyDominatedOn D m m') :=
  inferInstanceAs (Decidable ((∀ x ∈ D, m.eval x ≤ m'.eval x) ∧
    (∃ x ∈ D, m.eval x < m'.eval x)))

instance instDecIsStrictlyDominated {n : ℕ} (D : Finset (Fin n → ℝ))
    (p : TPoly n) (m : TPMonomial n) :
    Decidable (IsStrictlyDominated D p m) :=
  inferInstanceAs (Decidable (∃ m' ∈ p.support, m' ≠ m ∧ StrictlyDominatedOn D m m'))

namespace TPoly

/-- **Canonical pruning**: remove strictly dominated monomials.
    Falls back to `p` if the filter empties. -/
def canonicalOn {n : ℕ} (D : Finset (Fin n → ℝ)) (p : TPoly n) : TPoly n :=
  let filtered := p.support.filter (fun m => ¬IsStrictlyDominated D p m)
  if h : filtered.Nonempty then ⟨filtered, h⟩ else p



end TPoly

/-! ## Helper lemmas -/


/-
There exists a monomial achieving the sup'.
-/

/-
For strictly dominated m by m', if we follow the chain of strict dominations
    in a finite set, we eventually reach an undominated element with value ≥ m.
-/

/-! ## Theorem A: Canonical pruning preserves evaluation -/

/-
**Theorem A (Canonical Pruning Preserves Semantics).**

    Removing all monomials that are strictly dominated (≤ everywhere, < somewhere)
    on the domain does not change the evaluation at any domain point.

    The proof uses two key facts:
    1. Canonical support ⊆ original support, so canonical eval ≤ original eval.
    2. For each monomial m in the original support, there exists an undominated
       monomial m' with m'(x) ≥ m(x), because strict domination is acyclic on
       finite sets. Thus original eval ≤ canonical eval.
-/

/-! ## ReLU bridge -/

/-- ReLU function. -/
def reluFn (x : ℝ) : ℝ := max x 0


/-! ## Theorem B: ReLU-tropical pruning soundness -/

/-- Construct a tropical polynomial from an affine family. -/
def TPoly.ofAffineFamily {n k : ℕ} (A : Fin k → (Fin n → ℝ))
    (b : Fin k → ℝ) (hk : 0 < k) : TPoly n where
  support := Finset.univ.image (fun i => TPMonomial.mk (b i) (A i))
  nonempty := ⟨_, Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩


/-! ## Theorem C direction: essential monomials survive -/

/-
**Theorem C (Uniquely-Maximal Monomial Survives).**
    If `m` is *strictly* the maximum at some domain point (beats all other
    monomials), then `m` cannot be strictly dominated and thus survives
    canonical pruning.

    This is the interpretability direction: monomials with unique witness
    points are guaranteed to survive as essential decision templates.
-/

/-! ## Theorem D: Compression bound -/


end


