-- Prove2me | Definitions.Def_Applications_Algebra_TransitionEndomorphism
-- name    : Applications_Algebra_TransitionEndomorphism
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:44.911009+00:00
-- url     : https://prove2.me/theorems/d92fca36-cf66-4f69-af9a-3b552589c1c8
-- title:
--   Aether Catalog definitions — Applications_Algebra_TransitionEndomorphism
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Algebra.TransitionEndomorphism`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Algebra/TransitionEndomorphism.lean by skeleton subtraction
import Mathlib

/-!
# Transition endomorphisms of a discrete linear cocycle

This is a minimal, standalone finite-dimensional linear-algebra file.

Given a sequence of endomorphisms `f : ℕ → (V →ₗ[K] V)` of a vector space `V`,
the *transition endomorphism* `transEndo f i n` is the composite

  `f (i+n-1) ∘ ⋯ ∘ f (i+1) ∘ f i`

of the `n` endomorphisms starting at index `i`, with the convention
`transEndo f i 0 = id`.  This is the discrete analogue of the fundamental
solution / state-transition operator of a time-varying linear system.

The central structural fact is the **cocycle identity**
`transEndo f i (m + n) = transEndo f (i+n) m ∘ transEndo f i n`,
from which the monotone (antitone) behaviour of the rank sequence
`n ↦ finrank K (range (transEndo f i n))` follows immediately, *reusing*
Mathlib's existing rank-of-composite lemmas rather than re-deriving a
Sylvester inequality from scratch.

-- !-- Lab Notes -- !--
Hypothesis: The composite of a finite window of a sequence of endomorphisms
  obeys a one-parameter cocycle law in the window length, and the rank of the
  composite can only decrease as the window grows.
Experiment: Defined `transEndo` by recursion on the window length and proved the
  cocycle identity by induction; derived rank antitonicity from it.
Analysis: The cocycle identity is the load-bearing lemma. Once available, rank
  monotonicity is a one-line consequence of `Submodule.finrank_map_le` applied to
  `LinearMap.range_comp`; no bespoke Sylvester inequality is needed.
Critique: All main theorems use induction / the cocycle helper and are non-trivial
  (not `rfl`/`decide`). Finite dimensionality is only assumed where genuinely
  required (the rank statements), keeping the algebraic identities general.
Synthesis: A reusable transition-operator API with cocycle law, rank antitonicity,
  and an injectivity-propagation lemma.
-- !-- Lab Notes -- !--
-/

open LinearMap Module

namespace TransitionEndomorphism

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `transEndo f i n` is the composite `f (i+n-1) ∘ ⋯ ∘ f i` of the `n`
endomorphisms of the sequence `f` starting at index `i`. -/
def transEndo (f : ℕ → V →ₗ[K] V) (i : ℕ) : ℕ → V →ₗ[K] V
  | 0 => LinearMap.id
  | (n + 1) => (f (i + n)) ∘ₗ transEndo f i n





/-
The **cocycle identity**: composing a window of length `n` starting at `i`
with a window of length `m` starting at `i + n` yields the window of length
`m + n` starting at `i`.
-/

/-
Rank can only drop by extending the window by one step.
-/

/-
The rank sequence `n ↦ finrank (range (transEndo f i n))` is antitone:
a longer window has rank no larger than a shorter one.
-/

/-
If each endomorphism in the window is injective, so is the transition
endomorphism.
-/

end TransitionEndomorphism


