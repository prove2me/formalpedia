-- Prove2me | Theorems.Thm_TropEnvelope_envelopeCanonical_lower_bound
-- name    : TropEnvelope.envelopeCanonical_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:19:24.105499+00:00
-- url     : https://prove2.me/theorems/3431f5d5-37ee-4930-896f-fec7437e9476
-- title:
--   EnvelopeCanonical lower bound
-- statement:
--   Formal statement of `TropEnvelope.envelopeCanonical_lower_bound` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropEnvelope.envelopeCanonical_lower_bound    (p : Finset Mono) (hp : p.Nonempty)
--       (hgen : GenericPosition p)
--       (q : Finset Mono) (hq : q.Nonempty)
--       (hsub : q ⊆ p)
--       (hreal : ∀ n : ℕ, polyEval q hq (n : ℝ) = polyEval p hp (n : ℝ)) :
--       EnvelopeCanonical p ⊆ q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/EnvelopeCanonical.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/EnvelopeCanonical.lean#L238

-- Thm stub generated from Bridges/EnvelopeCanonical.lean
import Mathlib
import Definitions.Def_Bridges_EnvelopeCanonical

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

open TropEnvelope

/-! ## Core Type: Tropical Monomials -/







/-! ## Envelope Definitions -/





/-! ## Theorem 1: Semantics Preservation -/


/-! ## Theorem 2: Non-envelope characterization -/


/-! ## Theorem 3: Envelope Nonemptiness -/


/-! ## Genericity Hypotheses -/






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

theorem TropEnvelope.envelopeCanonical_lower_bound    (p : Finset Mono) (hp : p.Nonempty)
    (hgen : GenericPosition p)
    (q : Finset Mono) (hq : q.Nonempty)
    (hsub : q ⊆ p)
    (hreal : ∀ n : ℕ, polyEval q hq (n : ℝ) = polyEval p hp (n : ℝ)) :
    EnvelopeCanonical p ⊆ q := by sorry
