-- Prove2me | solution 1 for TropEnvelope.envelopeCanonical_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:03:17.467528+00:00
-- url     : https://prove2.me/submissions/d8d622dd-2026-4f08-94de-7aeb756431d6

-- Sol generated from Bridges/EnvelopeCanonical.lean
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

/-! ## Theorem 8: Exact Minimal Support (Flagship) -/


/-! ## Theorem 9: Semantic Equivalence -/


/-! ## Corollaries -/






open TropEnvelope in
theorem solution    (p : Finset Mono) (hp : p.Nonempty)
    (hgen : GenericPosition p)
    (q : Finset Mono) (hq : q.Nonempty)
    (hsub : q ⊆ p)
    (hreal : ∀ n : ℕ, polyEval q hq (n : ℝ) = polyEval p hp (n : ℝ)) :
    EnvelopeCanonical p ⊆ q := by
  -- We need to prove that every monomial in the envelope of p is also in q.
  -- We take an arbitrary monomial m from the envelope and show that it must be in q.
  intro m hm
  have hm_envelope_ess : EnvelopeEssential p m := by
    exact Finset.mem_filter.mp hm |>.2 |> fun ⟨ n, hn ⟩ => ⟨ Finset.mem_filter.mp hm |>.1, n, hn ⟩
  obtain ⟨m, hm_mem, hn⟩ := hm_envelope_ess;
  have h_inf_q : ∃ m₀ ∈ q, ∀ m' ∈ q, monoEval m₀ (hm_mem : ℝ) ≤ monoEval m' (hm_mem : ℝ) := by
    exact Finset.exists_min_image _ _ hq;
  have h_inf_eq : polyEval q hq (hm_mem : ℝ) = polyEval p hp (hm_mem : ℝ) := by
    exact hreal hm_mem
  have h_inf_eq' : polyEval q hq (hm_mem : ℝ) = monoEval (‹_› : Mono) (hm_mem : ℝ) := by
    exact h_inf_eq.trans ( le_antisymm ( Finset.inf'_le _ m ) ( Finset.le_inf' _ _ fun x hx => hn x hx ) )
  have h_inf_eq'' : monoEval (‹_› : Mono) (hm_mem : ℝ) = monoEval (h_inf_q.choose : Mono) (hm_mem : ℝ) := by
    have h_inf_eq'' : polyEval q hq (hm_mem : ℝ) = monoEval (h_inf_q.choose : Mono) (hm_mem : ℝ) := by
      exact le_antisymm ( Finset.inf'_le _ h_inf_q.choose_spec.1 ) ( Finset.le_inf' _ _ fun x hx => h_inf_q.choose_spec.2 x hx );
    exact h_inf_eq'.symm.trans h_inf_eq''
  have h_inf_eq''' : ‹_› = h_inf_q.choose := by
    exact Classical.not_not.1 fun h => hgen ( show _ ∈ p from m ) ( show _ ∈ p from hsub h_inf_q.choose_spec.1 ) h hm_mem h_inf_eq''
  have h_inf_eq'''' : ‹_› ∈ q := by
    exact h_inf_eq'''.symm ▸ h_inf_q.choose_spec.1
  exact h_inf_eq''''
