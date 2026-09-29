-- Prove2me | Definitions.Def_Bridges_EnvelopeCanonical
-- name    : Bridges_EnvelopeCanonical
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:04.149992+00:00
-- url     : https://prove2.me/theorems/4f6d6078-d789-4b4e-a55e-04709927fc04
-- title:
--   Aether Catalog definitions — Bridges_EnvelopeCanonical
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.EnvelopeCanonical`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/EnvelopeCanonical.lean by skeleton subtraction
import Mathlib

/-!
# Envelope Canonicalization and Exact Minimization for Tropical Polynomials

This file establishes that the **lower-envelope support** of a tropical polynomial —
the subfamily of monomials that actually attain the pointwise minimum somewhere on `ℕ` —
is the exact **semantic core** governing minimal support realization.

## Mathematical Context

A tropical polynomial in one variable is `p(x) = min_i (cᵢ + eᵢ · x)`, the lower
envelope of finitely many affine functions. **Pareto canonicalization** (ℕ-canonical form)
removes monomials pointwise dominated by a single competitor. But a monomial can
survive Pareto pruning while still never lying on the lower envelope, hidden by a
*coalition* of competitors.

**Envelope canonicalization** detects this coalition-domination: a monomial is
envelope-essential iff it actually attains the minimum somewhere on `ℕ`.

Under the **generic position** hypothesis (no two distinct monomials agree at any
natural number), envelope canonicalization becomes an **exact** minimization:
- Every envelope monomial has a **strict unique witness**
- Removing ANY envelope monomial changes the weighted language
- Every sub-polynomial preserving semantics must contain the envelope
- The envelope is the unique minimum-cardinality support

## Main Results

* `eval_envelopeCanonical_eq` — semantics preservation: envelope evaluates identically on ℕ
* `envelopeCanonical_nonempty` — nonemptiness of envelope for nonempty polynomials
* `not_mem_envelopeCanonical_iff_never_minimizes` — non-envelope characterization
* `distinctSlopes_implies_pairwiseDistinct` — distinct slopes ⟹ distinct functions
* `envelope_unique_witness_of_generic` — strict witness under generic position
* `envelope_subset_natCanonical_of_generic` — envelope ⊆ NatCanonical under genericity
* `envelope_monomial_indispensable` — strict-witness monomials are indispensable
* `envelopeCanonical_lower_bound` — every realizing sub-polynomial contains envelope
* `envelopeCanonical_is_minimal_support` — **flagship**: envelope is exact minimal support
* `envelopeCanonical_semantic_equiv` — semantic equivalence from envelope equality
-/

noncomputable section

open Classical

namespace TropEnvelope

/-! ## Core Type: Tropical Monomials -/

/-- A tropical monomial: the affine function `coeff + exp · x`. -/
structure Mono where
  exp : ℕ
  coeff : ℝ
  deriving DecidableEq

/-- Evaluate a monomial at a real-valued point. -/
@[simp]
def monoEval (m : Mono) (x : ℝ) : ℝ := m.coeff + (m.exp : ℝ) * x

/-- Evaluate a tropical polynomial (finset of monomials) at a point: minimum over monomials. -/
def polyEval (p : Finset Mono) (hp : p.Nonempty) (x : ℝ) : ℝ :=
  p.inf' hp (fun m => monoEval m x)

/-- The weighted language of a tropical polynomial. -/
def polyLanguage (p : Finset Mono) (hp : p.Nonempty) : ℕ → ℝ :=
  fun n => polyEval p hp (n : ℝ)

/-- ℕ-dominance: `m₁` dominates `m₂` on all natural numbers. -/
def NatDominates (m₁ m₂ : Mono) : Prop :=
  ∀ n : ℕ, monoEval m₁ (n : ℝ) ≤ monoEval m₂ (n : ℝ)

/-- The ℕ-canonical form: keep monomials not dominated by any other on ℕ. -/
def NatCanonical (p : Finset Mono) : Finset Mono :=
  p.filter (fun m => ¬ ∃ m' ∈ p, m' ≠ m ∧ NatDominates m' m)

/-! ## Envelope Definitions -/

/-- A monomial `m` is **envelope-essential** in `p` if it actually attains the minimum
    of the polynomial at some natural number point. -/
def EnvelopeEssential (p : Finset Mono) (m : Mono) : Prop :=
  m ∈ p ∧ ∃ n : ℕ, ∀ m' ∈ p, monoEval m (n : ℝ) ≤ monoEval m' (n : ℝ)

/-- The **envelope-canonical form**: the subset of monomials that are envelope-essential. -/
def EnvelopeCanonical (p : Finset Mono) : Finset Mono :=
  p.filter (fun m => ∃ n : ℕ, ∀ m' ∈ p, monoEval m (n : ℝ) ≤ monoEval m' (n : ℝ))



/-! ## Theorem 1: Semantics Preservation -/


/-! ## Theorem 2: Non-envelope characterization -/


/-! ## Theorem 3: Envelope Nonemptiness -/


/-! ## Genericity Hypotheses -/

/-- Monomials in a finset have **distinct slopes** (pairwise distinct exponents). -/
def DistinctSlopes (p : Finset Mono) : Prop :=
  ∀ {m₁ m₂ : Mono}, m₁ ∈ p → m₂ ∈ p → m₁.exp = m₂.exp → m₁ = m₂

/-- Monomials are **pairwise distinct as functions** on ℕ. -/
def PairwiseDistinctFunctions (p : Finset Mono) : Prop :=
  ∀ {m₁ m₂ : Mono}, m₁ ∈ p → m₂ ∈ p →
    (∀ n : ℕ, monoEval m₁ (n : ℝ) = monoEval m₂ (n : ℝ)) → m₁ = m₂

/-- **Generic position**: no two distinct monomials agree at any natural number.
    This is the natural genericity condition for discrete tropical geometry:
    the crossing points of affine functions avoid the integer lattice. -/
def GenericPosition (p : Finset Mono) : Prop :=
  ∀ {m₁ m₂ : Mono}, m₁ ∈ p → m₂ ∈ p → m₁ ≠ m₂ →
    ∀ n : ℕ, monoEval m₁ (n : ℝ) ≠ monoEval m₂ (n : ℝ)



/-! ## Theorem 4: Strict Witness under Generic Position -/

/-
**Strict witness theorem under generic position.**
    If no two distinct monomials agree at any natural number, then every
    envelope monomial has a witness where it is the **strict unique** minimizer.

    Proof: `m ∈ EnvelopeCanonical p` gives a witness `n₀` with
    `monoEval m n₀ ≤ monoEval m' n₀` for all `m' ∈ p`. By generic position,
    `m ≠ m'` implies `monoEval m n₀ ≠ monoEval m' n₀`, so the inequality
    must be strict.
-/

/-! ## Theorem 5: Envelope ⊆ NatCanonical under Genericity -/

/-
Under generic position, every envelope-essential monomial is Pareto-essential.
    The strict witness from `envelope_unique_witness_of_generic` prevents domination.
-/

/-! ## Theorem 6: Indispensability from Strict Witness -/

/-
A monomial with a strict witness is **indispensable**: removing it changes
    the polynomial evaluation at the witness point.

    This holds without any genericity hypothesis — it follows purely from
    the definition of strict minimum.
-/

/-! ## Theorem 7: Lower Bound on Realization Size -/

/-
**Lower bound theorem.**
    Under generic position, any sub-polynomial of `p` that realizes the same
    language must contain all envelope monomials.

    Proof: Each `m ∈ EnvelopeCanonical p` has a strict witness `n_m`. Any
    sub-polynomial `q ⊆ p` with `polyEval q = polyEval p` on ℕ must achieve
    `polyEval q n_m = monoEval m n_m`. Since `q ⊆ p`, some `m' ∈ q ⊆ p`
    has `monoEval m' n_m ≤ monoEval m n_m`. By strictness, `m' = m`.
-/

/-! ## Theorem 8: Exact Minimal Support (Flagship) -/


/-! ## Theorem 9: Semantic Equivalence -/


/-! ## Corollaries -/




end TropEnvelope

end


