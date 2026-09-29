-- Prove2me | Definitions.Def_Novelty_CrossIntersectingProductGeneral
-- name    : Novelty_CrossIntersectingProductGeneral
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:10:06.030921+00:00
-- url     : https://prove2.me/theorems/2470156c-478a-45ab-adfd-c0d73c24e108
-- title:
--   Aether Catalog definitions — Novelty_CrossIntersectingProductGeneral
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CrossIntersectingProductGeneral`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CrossIntersectingProductGeneral.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cross-intersecting product bound over an arbitrary finite ground set

The companion file `Novelty.CrossIntersectingProductBound` proves the multilateral
cross-intersecting product skeleton for families of subsets of `Fin n`.  Here we
lift the same argument to subsets of an **arbitrary finite type** `α`, with the
elementary count `g(|α|, k) = C(|α|,k) - C(|α|-k,k)`.  This is the natural, label-free
home for the result: the only role of the ground set is its cardinality.

This file is deliberately self-contained (it imports only Mathlib) so that the core
mechanism — a single member of one family pins the size of every cross-intersecting
partner — is available for any finite vertex set.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The `Fin n` proof never uses the order on `Fin n`; only
  `Fintype.card` matters, so the whole development should generalise verbatim.
Experiment (Experimenter): Re-stated `IsUniform`, `CrossIntersecting`, `gcard` and
  the per-family count over `[Fintype α] [DecidableEq α]`, replacing `n` by
  `Fintype.card α` and `Finset.card_univ` doing the bookkeeping.
Analysis (Analyst): Confirmed the argument is purely about cardinalities: the
  counting set `powersetCard k univ \ powersetCard k A₀ᶜ` and `card_compl` are all
  type-agnostic.  The generalisation costs nothing and clarifies what the theorem
  "is about".
Critique (Critic): To avoid a vacuous statement on empty `α`, the bound is an honest
  `Finset.card` inequality that holds for all `α`; when no `k`-set exists both sides
  are governed by the same `choose` arithmetic.
Synthesis (PI): A ground-set-agnostic multilateral cross-intersecting product bound.
-/

open Finset

namespace CrossIntersectingProductGeneral

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `𝓕` is `k`-uniform: every member has exactly `k` elements. -/
def IsUniform (k : ℕ) (𝓕 : Finset (Finset α)) : Prop := ∀ A ∈ 𝓕, A.card = k

/-- Two families are *cross-intersecting* if every member of one meets every
member of the other. -/
def CrossIntersecting (𝓕 𝓖 : Finset (Finset α)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓖, (A ∩ B).Nonempty

/-- The "fixed-set meeting count" over a ground set of size `Fintype.card α`. -/
def gcard (α : Type*) [Fintype α] (k : ℕ) : ℕ :=
  Nat.choose (Fintype.card α) k - Nat.choose (Fintype.card α - k) k

/-
**Per-family bound (general ground set).** If `𝓖` is `k`-uniform and every
member meets a fixed `k`-set `A₀`, then `|𝓖| ≤ gcard α k`.
-/

/-
**Multilateral cross-intersecting product bound (general ground set).** For
`r ≥ 2` non-empty, `k`-uniform, pairwise cross-intersecting families of subsets of
a finite type `α`, the product of their sizes is at most `gcard α k ^ r`.
-/

end CrossIntersectingProductGeneral


