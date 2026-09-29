-- Prove2me | Theorems.Thm_ShearedWittTropical_sheared_double_colimit
-- name    : ShearedWittTropical.sheared_double_colimit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:38:09.794219+00:00
-- url     : https://prove2.me/theorems/09469362-6a7b-4f95-b616-8eb87dfeb48b
-- title:
--   **Sheared Witt vectors are the double filtered colimit of truncated Witt
-- statement:
--   **Sheared Witt vectors are the double filtered colimit of truncated Witt
--   vectors.**  Let `S : ι → Subring R` be a monotone family over a nonempty directed
--   index, with colimit the subring `⨆ i, S i`.  Then the coordinate sequences of the
--   sheared Witt vectors over the colimit ring `⨆ i, S i` (finite support, all
--   coordinates in the colimit) are *exactly* the directed union, over truncation
--   level `n` and ring stage `i`, of the truncated coordinate sequences over the stage
--   `S i` (vanishing beyond `n`, all coordinates in `S i`).
--
--   This is `χW ≅ colimₙ W(R[pⁿ])/ĥw(R[pⁿ])` in the concrete directed-union model of a
--   filtered colimit of rings: the colimit in the *base ring* variable `i` and the
--   colimit in the *arity/truncation* variable `n` fuse into a single directed union
--   computing the sheared object.
--
--   ```lean
--   theorem ShearedWittTropical.sheared_double_colimit    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
--       {S : ι → Subring R} (hmono : Monotone S) :
--       (⋃ i : ι, ⋃ n : ℕ, {g : ℕ → R | (∀ k, n ≤ k → g k = 0) ∧ ∀ k, g k ∈ S i})
--         = {g : ℕ → R | (∃ N, ∀ k ≥ N, g k = 0) ∧ ∀ k, g k ∈ ⨆ i, S i} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/ShearedWitt/Colimit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/ShearedWitt/Colimit.lean#L109

-- Thm stub generated from Tropical/ShearedWitt/Colimit.lean
import Mathlib
import Definitions.Def_Tropical_ShearedWitt_Colimit
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sheared Witt vectors as the (double) filtered colimit of truncated Witt vectors

This file gives a concrete, self-contained proof of the identification

  *the sheared Witt vector functor is the filtered colimit of the truncated Witt
   vector functors* (Drinfeld–Lau 2025; Zink 2003; Lau 2010; Hoff–Lau 2026),

realised at the two levels a filtered colimit genuinely happens in:

* **Arity direction** (`iUnion_trunc_eq_sheared`): with a fixed basepoint `b`,
  the sequences that are *eventually `b`* (finite essential support — the
  *sheared* object) are exactly the directed union over `n` of the sequences that
  are `b` *beyond coordinate `n`* (the *truncated* objects, set-theoretically
  `Wₙ = Aⁿ` extended by `b`).  This is the shearing mechanism in isolation.

* **Base-ring direction fused with the arity direction**
  (`sheared_double_colimit`): for a monotone directed family of subrings
  `S : ι → Subring R` with colimit `⨆ i, S i`, the sheared Witt coordinate
  sequences over the colimit ring are *exactly* the double directed union, over
  truncation level `n` and stage `i`, of truncated coordinate sequences over the
  stage `S i`.  This is the full statement `χW ≅ colim_n W(R[pⁿ])/ĥw(R[pⁿ])`
  transported to the concrete "directed union of subrings" model of a filtered
  colimit of rings.

* **Genuine Witt vectors** (`shearedWitt_colimit`): the same statement for
  Mathlib's honest `WittVector p R`, produced through the functorial
  `WittVector.map (S i).subtype`.

* **Necessity of shearing** (`naiveWitt_colimit_fails`): the unrestricted
  (big / naive) Witt functor does *not* preserve the colimit — an explicit,
  natural counterexample over a polynomial ring shows the finite-support
  hypothesis cannot be dropped.

A tropical (min–plus) corollary `tropical_sheared_eq_colimit_truncated` records
that the shearing mechanism is not special to Witt vectors: over the tropical
semiring `Tropical (WithTop ℕ)` the finitely-supported (eventually-`0`, i.e.
eventually tropical-`∞`) vectors are again the colimit of the truncated ones.

-- !-- Lab Notes -- !--
Hypothesis (Stage 1): ranked falsifiable conjectures.
  (C1)[flagship, PROVED as `sheared_double_colimit`] The sheared Witt coordinate
       functor over a filtered colimit of rings `⨆ Sᵢ` is the *double* colimit,
       over truncation level and ring stage, of truncated Witt over the stages.
       Impact: this is the entire mission statement in one equation, not just the
       one-directional "lift exists".
  (C2, surprising)[PROVED as `naiveWitt_colimit_fails`] Drop finite support and
       C1 is FALSE for genuine Witt vectors, witnessed by the "vector of all
       variables" over `MvPolynomial ℕ K`: every coordinate lifts, the whole
       vector does not.
  (C3)[PROVED as `shearedWitt_colimit`] C1 upgrades from coordinate sequences to
       Mathlib's honest `WittVector p R` via `WittVector.map`.
  (C4, cross-domain)[PROVED as `tropical_sheared_eq_colimit_truncated`] The
       shearing = colimit-of-truncations phenomenon is a statement about
       eventually-basepoint sequences, hence holds verbatim on the tropical
       semiring; Witt vs. tropical differ only in the choice of basepoint.
  (C5, considered) `⋃ i, varSubring K i = ⊤` — scaffolding for C2, not billed.
Experiment (Stage 2): the colimit engine is `Finset.exists_le` (directed + finite
  ⇒ single upper bound); the arity engine is a case split at the support bound
  `N`.  The genuine-Witt bridge is a direct `WittVector.mk`/`WittVector.ext`
  packaging.  Prototyped against `WittVector.{mk,coeff,map,map_coeff,ext,coeff_mk}`
  and `Subring.mem_iSup_of_directed`.
Analysis (Stage 3): C1 is "true, and the fusion of two colimits is the real
  content": the ⊇ direction merges finitely many stage-witnesses AND a support
  bound at once.  C2 is "true and the interesting failure": genuinely false, not
  merely hard — the obstruction `X (i+1) ∈ varSubring K i` is an arithmetic
  contradiction `i+1 ∈ range (i+1)`.
Critique (Stage 4): no result is `simp`/`decide`-only.  C1/C3 combine directed
  merging with an explicit construction; C2 is an honest `by_contra`-style
  disproof; C4 is a genuine specialisation, not a rename.  `Nontrivial K` is
  required (for `vars_X`) and stated.
Synthesis (Stage 5): over any commutative ring presented as a filtered colimit of
  subrings, the sheared Witt vectors are the colimit of the truncated Witt
  vectors — in both the arity and the base-ring variable — and shearing (finite
  support) is exactly the minimal repair that makes the infinite-arity Witt
  functor preserve the colimit.  The mechanism is basepoint-agnostic, giving a
  clean Witt ⇄ tropical bridge.
-- !-- end Lab Notes -- !--
-/

open scoped BigOperators
open MvPolynomial

open ShearedWittTropical

/-! ## The shearing mechanism in isolation: sheared = colimit of truncated -/

/-
**Sheared = colimit of truncated, arity direction.**
For any type `A` and basepoint `b : A`, the *sheared* set of sequences that are
eventually equal to `b` (finite essential support) is exactly the directed union,
over the truncation level `n`, of the *truncated* sets of sequences that are equal
to `b` beyond coordinate `n`.

Set-theoretically a truncated Witt vector `Wₙ(A)` is `Aⁿ`, embedded into `A^ℕ` by
padding with the basepoint; this lemma says the sheared functor `χW` is the
filtered colimit `colimₙ Wₙ` of these truncations.
-/

/-! ## The full statement: sheared Witt over a filtered colimit of rings -/

theorem ShearedWittTropical.sheared_double_colimit    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {S : ι → Subring R} (hmono : Monotone S) :
    (⋃ i : ι, ⋃ n : ℕ, {g : ℕ → R | (∀ k, n ≤ k → g k = 0) ∧ ∀ k, g k ∈ S i})
      = {g : ℕ → R | (∃ N, ∀ k ≥ N, g k = 0) ∧ ∀ k, g k ∈ ⨆ i, S i} := by sorry
