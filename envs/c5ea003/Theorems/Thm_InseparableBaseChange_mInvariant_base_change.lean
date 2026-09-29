-- Prove2me | Theorems.Thm_InseparableBaseChange_mInvariant_base_change
-- name    : InseparableBaseChange.mInvariant_base_change
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:53:11.764659+00:00
-- url     : https://prove2.me/theorems/4a77ca90-d813-4af9-9089-b8bcafdfa806
-- title:
--   Main Theorem.
-- statement:
--   **Main Theorem.**  Invariance of the field invariant `m_f` under purely inseparable base
--   change.  If `N/K` is purely inseparable (inside a common overfield `M`) and `θ ∈ M` is algebraic
--   over `K`, then the separable degree of the minimal polynomial of `θ` is unchanged when the base
--   is enlarged from `K` to `N`:  `m_{f,N} = m_f`.
--
--   ```lean
--   theorem InseparableBaseChange.mInvariant_base_change    (N : Type*) [Field N] [Algebra K N] [Algebra N M] [IsScalarTower K N M]
--       [IsPurelyInseparable K N] (θ : M) (hθ : IsAlgebraic K θ) :
--       mInvariant N θ = mInvariant K θ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/InseparableBaseChange/Invariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/InseparableBaseChange/Invariance.lean#L109

-- Thm stub generated from Applications/InseparableBaseChange/Invariance.lean
import Mathlib
import Definitions.Def_Applications_InseparableBaseChange_Invariance
/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Invariance of the field invariant `m_f` under purely inseparable base change

Let `L = K(θ)` be a simple algebraic field extension in characteristic `p > 0`, with minimal
polynomial `f = minpoly K θ ∈ K[X]`.  The paper under study attaches to such an extension a
numerical invariant `m_f`, used to formulate a criterion for the compositum to split as the
product of its maximal purely inseparable and maximal separable subextensions.

The correct base-change-invariant choice of `m_f` is the **separable degree of `f`**, i.e. the
number of *distinct* roots of `f` in a splitting field.  Equivalently, if we factor the
irreducible `f` as `f(X) = g(X^{p^e})` with `g` separable irreducible, then `m_f = deg g`, the
separable part of the degree.  In Lean this is `Polynomial.natSepDegree (minpoly K θ)`.

## Main results

* `InseparableBaseChange.mInvariant` — the invariant `m_f := (minpoly K θ).natSepDegree`.
* `InseparableBaseChange.mInvariant_base_change`
    (**Main Theorem**) — for any purely inseparable extension `N/K` (inside a common field `M`)
    and any `θ ∈ M` algebraic over `K`, the invariant of `θ` computed over `N` equals the
    invariant computed over `K`:  `m_{f,N} = m_f`.  Hence the invariant depends only on `L/K`
    and not on the choice of purely inseparable base extension `N/K`.
* `InseparableBaseChange.finSepDegree_simple_base_change` — the same statement phrased via
    `Field.finSepDegree` of the simple extensions `N(θ)/N` and `K(θ)/K`.

The proof combines three facts from the Mathlib field-theory library:

1. `Field.finSepDegree_eq` : for an algebraic extension the (finite) separable degree equals
   `Cardinal.toNat` of the cardinal-valued separable degree;
2. `IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree` : the separable degree of a
   simple extension equals the `natSepDegree` of the minimal polynomial; and
3. `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'` : separable
   degree is invariant under purely inseparable base change (which itself rests on the linear
   disjointness of separable and purely inseparable extensions).

The new content here is the *packaging of these into the polynomial invariant* `m_f`, plus the
adjoin-compositum identification `adjoin N (K⟮θ⟯ : Set M) = N⟮θ⟯` that bridges the abstract
intermediate-field statement to the concrete `minpoly`-level invariant of the paper.

## Lab Notes

-- !-- Lab Notes -- !--
**Hypothesis (Hypothesizer).**  Several candidate definitions of `m_f` were proposed:
  (H1) the inseparable *exponent* `e` (so that `f(X) = g(X^{p^e})`);
  (H2) the inseparable *degree* `p^e = [L:K]_i`;
  (H3) the separable degree `[L:K]_s = deg g = (minpoly K θ).natSepDegree`.
The bold conjecture was: *some* numerical invariant of `f` is invariant under purely inseparable
base change `N/K`, and identifying the right one pins down the splitting criterion intrinsically.

**Experiment (Experimenter).**  Test case `K = 𝔽_p(a)`, `θ = a^{1/p}` (so `L/K` purely
inseparable, exponent `e = 1`).  Take `N = K(a^{1/p}) = L`.  Then `NL = N` and `θ ∈ N`, so the
minimal polynomial of `θ` over `N` is `X - θ`: inseparable exponent drops to `0` and inseparable
degree drops from `p` to `1`.  Hence **(H1) and (H2) are FALSE** — the inseparable data is not
base-change invariant.  In that same example the separable degree is `1` both over `K` and over
`N`, consistent with (H3).

**Analysis (Analyst).**  (H3) survives and is provable in full generality: separable degree is
preserved because a separable and a purely inseparable extension of `K` are linearly disjoint, so
adjoining `N` cannot merge any of the distinct roots of the separable part `g`.  The failure of
(H1)/(H2) is structural: purely inseparable base change can *absorb* part (or all) of the
inseparable tower, but it never touches the separable part.  "True but hard" was avoided by
reducing to the Mathlib lemma `sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'`.

**Critique (Critic).**  The result is non-trivial (it fails for the naive inseparable invariants,
as the counterexample shows) and is not a definitional unfolding: the proof passes through the
adjoin-compositum identity and the cardinal/`ℕ` separable-degree comparison.  No hypothesis is
vacuous; `IsPurelyInseparable K N` is load-bearing (drop it and the conclusion is false, e.g. for
a separable `N/K` enlarging the splitting field of `g`).

**Synthesis (PI).**  Define `m_f := (minpoly K θ).natSepDegree`; this is the invariant for which
`m_{f,N} = m_f` holds, and it is exactly the number of distinct roots of `f`.
-- !-- Lab Notes -- !--
-/

open IntermediateField Field Polynomial

open InseparableBaseChange

set_option maxHeartbeats 1200000

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

theorem InseparableBaseChange.mInvariant_base_change    (N : Type*) [Field N] [Algebra K N] [Algebra N M] [IsScalarTower K N M]
    [IsPurelyInseparable K N] (θ : M) (hθ : IsAlgebraic K θ) :
    mInvariant N θ = mInvariant K θ := by sorry
