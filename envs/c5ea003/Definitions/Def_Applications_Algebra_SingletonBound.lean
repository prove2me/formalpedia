-- Prove2me | Definitions.Def_Applications_Algebra_SingletonBound
-- name    : Applications_Algebra_SingletonBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:39.718979+00:00
-- url     : https://prove2.me/theorems/d97f8e6d-8521-47e2-a3a4-26a65ffc4c7a
-- title:
--   Aether Catalog definitions — Applications_Algebra_SingletonBound
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Algebra.SingletonBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Algebra/SingletonBound.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.

# The Singleton Bound for Block Codes

## Overview

This file proves the **Singleton bound** of coding theory inside the same
combinatorial framework as `Catalog/Tropical/SpherePackingBound.lean` and
`Catalog/Applications/GilbertVarshamov.lean` (words `ι → G`, Hamming metric):

      |C| ≤ qⁿ⁻ᵈ⁺¹       for any `d`-separated code `C ⊆ (ι → G)`,

where `n = |ι|`, `q = |G|`. Unlike the sphere-packing and Gilbert–Varshamov
bounds, the Singleton bound needs **no group structure on the alphabet** and no
ball-volume formula: it is a pure *projection-injectivity* argument.

## Main Results

* `restriction_injOn` — erasing `d-1` coordinates is injective on a `d`-separated
  code (two codewords differing in `≥ d` places cannot agree on `n-d+1` places).
* `singleton_bound` — `|C| ≤ qⁿ⁻ᵈ⁺¹`.

## Catalog Synthesis

Complements `SpherePackingBound.sphere_packing_bound` (upper bound via packing)
and `GilbertVarshamov.gilbert_varshamov` (lower bound via covering) with the
*third* classical bound — Singleton — completing the trio of elementary code-size
estimates over q-ary alphabets. The key technical hinge, that `hammingDist` is the
cardinality of the disagreement `Finset`, is shared with both companion files.

-- !-- Lab Notebook -- !--
Hypothesis: a metric separation hypothesis (min distance `≥ d`) can be converted
  into a cardinality bound by *projecting away* `d-1` coordinates injectively.
Result: proved `singleton_bound` (`|C| ≤ qⁿ⁻ᵈ⁺¹`) via `restriction_injOn` and
  `Finset.card_le_card_of_injOn`.
Insight: injectivity is immediate because if two codewords agreed on a set `T`
  with `|Tᶜ| ≤ d-1`, their disagreement set would sit inside `Tᶜ`, forcing
  `hammingDist < d` — contradicting separation. No alphabet structure is used.
Failure analysis: a naive "project onto the first `n-d+1` coordinates" stumbles on
  the abstract index type `ι`; the fix is `Finset.exists_subset_card_eq` to *pick*
  a coordinate set of the right size rather than relying on an ordering.
-/

open Finset BigOperators

noncomputable section

namespace SingletonBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : Type*} [Fintype G] [DecidableEq G]

/-- A code is `d`-**separated** if any two distinct codewords are at Hamming
    distance at least `d`. -/
def Separated (C : Finset (ι → G)) (d : ℕ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y

/-
!-- If `x, y ∈ C` agree on a coordinate set `T` whose complement has size `≤ d-1`,
then their disagreement set is contained in `Tᶜ`, so `hammingDist x y ≤ |Tᶜ| < d`,
contradicting `d`-separation; hence `x = y`. -- !--

**Restriction is injective.** On a `d`-separated code, restricting words to a
coordinate set `T` with `|Tᶜ| ≤ d - 1` is injective.
-/

/-
!-- Pick (via `Finset.exists_subset_card_eq`) a coordinate set `T` of size
`n-(d-1)`; its complement has size `d-1`, so `restriction_injOn` makes the
restriction `C → (T → G)` injective, whence `|C| ≤ |T → G| = q^{n-d+1}`. -- !--

**Singleton bound.** A `d`-separated code with `d - 1 ≤ n` has `|C| ≤ qⁿ⁻ᵈ⁺¹`.
(The classical statement also assumes `1 ≤ d`; this hypothesis turns out to be
unnecessary — with `ℕ` truncated subtraction the bound is vacuously `|C| ≤ qⁿ`
when `d = 0` — so we omit it for a strictly more general result.)
-/

end SingletonBound
end


