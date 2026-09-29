-- Prove2me | Definitions.Def_Novelty_CrossIntersectingProductBound
-- name    : Novelty_CrossIntersectingProductBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:10:08.078015+00:00
-- url     : https://prove2.me/theorems/e3e8bf65-b9b3-434a-8c19-623ab30e7948
-- title:
--   Aether Catalog definitions — Novelty_CrossIntersectingProductBound
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CrossIntersectingProductBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CrossIntersectingProductBound.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A multilateral cross-intersecting product bound

This file studies the *multilateral* (more than two) cross-intersecting product
problem behind the Frankl–Wang conjecture:

> For `n ≥ 2k`, `k ≥ 3`, `r ≥ 2`, if `(𝓕ᵢ)_{i : Fin r}` are `k`-uniform families
> of subsets of `Fin n` that are **non-trivial** (none contained in a star) and
> **pairwise cross-intersecting**, then `∏ᵢ |𝓕ᵢ| ≤ h(n,k)^r`, where
> `h(n,k) = C(n-1,k-1) - C(n-k-1,k-1) + 1` is the Hilton–Milner value.

The sharp Hilton–Milner exponent base `h(n,k)` is the deep part of the conjecture
(it is, even for `r = 2`, a Hilton–Milner-type extremal result not currently in
Mathlib).  What we prove here, *unconditionally and fully*, is the **uniform
cross-intersecting product bound**

    ∏ᵢ |𝓕ᵢ| ≤ (C(n,k) - C(n-k,k))^r,

i.e. the multilateral product bound with the elementary "fixed-set meeting count"
`g(n,k) := C(n,k) - C(n-k,k)` in place of the Hilton–Milner value.  This is the
first-moment skeleton of the conjecture: it uses `r ≥ 2`, uniformity, and the
pairwise cross-intersection hypothesis in an essential way, and it is exactly the
bound one obtains *before* exploiting non-triviality to sharpen `g(n,k)` down to
`h(n,k)`.

## Catalog connections
* `Erdős–Ko–Rado theorem for intersecting uniform families`: `card_le_of_cross`
  is the cross-family analogue of the "a set meets at most `C(n,k) - C(n-k,k)`
  many `k`-sets" count underlying EKR.
* `Pyber product theorem for two cross-intersecting families`: `prod_card_le_pow`
  specialised to `r = 2` is the elementary (non-sharp) Pyber-type product bound.
* `Frankl–Wang non-trivial cross-intersection product conjecture`: the headline
  `multilateral_cross_product_bound` is the unconditional skeleton of that
  conjecture; sharpening `g(n,k)` to the Hilton–Milner `h(n,k)` is recorded as a
  future direction.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The multilateral product `∏ᵢ |𝓕ᵢ|` for pairwise
  cross-intersecting `k`-uniform families is controlled by a per-family bound:
  each family is "pinned" by a single member of another family.
Experiment (Experimenter): For a fixed `A₀` of size `k`, every `B` meeting `A₀`
  lies in `powersetCard k univ \ powersetCard k A₀ᶜ`, of size `C(n,k) - C(n-k,k)`.
  With `r ≥ 2` every index `i` has a partner `j ≠ i`, supplying such an `A₀ ∈ 𝓕ⱼ`.
  The product then collapses by `prod_le_prod'` + `prod_const`.
Analysis (Analyst): The hypotheses pull their weight: `r ≥ 2` provides the partner
  family, nonemptiness provides `A₀`, uniformity makes the count clean, and
  cross-intersection is exactly "`B` is not a `k`-subset of `A₀ᶜ`".  The only piece
  NOT used is non-triviality — which is precisely the lever that, in Frankl–Wang,
  improves `g(n,k) = C(n,k) - C(n-k,k)` to the Hilton–Milner `h(n,k)`.
Critique (Critic): `g(n,k)` is genuinely weaker than `h(n,k)`, so this is an honest
  *skeleton*, not the full conjecture; we name the gap explicitly.  The bound is not
  vacuous: `card_le_of_cross` is a true `Finset.card` inequality, `crossIntersecting`
  is the honest pairwise definition, and the product theorem degrades gracefully to
  `0` when a family is empty.
Synthesis (PI): A clean, unconditional multilateral cross-intersecting product
  bound, with the Hilton–Milner sharpening isolated as the remaining open step.
-/

open Finset

namespace CrossIntersectingProduct

variable {n : ℕ}

/-- `𝓕` is `k`-uniform: every member has exactly `k` elements. -/
def IsUniform (k : ℕ) (𝓕 : Finset (Finset (Fin n))) : Prop := ∀ A ∈ 𝓕, A.card = k

/-- `𝓕` is contained in a *star*: some fixed point lies in every member. -/
def IsStar (𝓕 : Finset (Finset (Fin n))) : Prop := ∃ x, ∀ A ∈ 𝓕, x ∈ A

/-- `𝓕` is *non-trivial* if it is not contained in any star. -/
def NonTrivial (𝓕 : Finset (Finset (Fin n))) : Prop := ¬ IsStar 𝓕

/-- Two families are *cross-intersecting* if every member of one meets every
member of the other. -/
def CrossIntersecting (𝓕 𝓖 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓖, (A ∩ B).Nonempty


/-- The elementary "fixed-set meeting count" `g(n,k) = C(n,k) - C(n-k,k)`: the
number of `k`-subsets of `[n]` meeting a fixed `k`-set. -/
def g (n k : ℕ) : ℕ := Nat.choose n k - Nat.choose (n - k) k






/-! ## Corollaries and an explicit non-vacuity witness -/


/-- The fixed `3`-set used by the explicit witness. -/
def witnessCore : Finset (Fin 6) := {1, 2, 3}

/-- A Hilton–Milner family on `Fin 6`: the `3`-sets containing `0` and meeting
`{1,2,3}`, together with `{1,2,3}` itself. -/
def hiltonMilnerWitness : Finset (Finset (Fin 6)) :=
  ((univ : Finset (Fin 6)).powersetCard 3).filter
    (fun B => (0 ∈ B ∧ (B ∩ witnessCore).Nonempty) ∨ B = witnessCore)





/-- The two-copy multilateral family built from the witness. -/
def witnessFamily : Fin 2 → Finset (Finset (Fin 6)) := fun _ => hiltonMilnerWitness


end CrossIntersectingProduct


