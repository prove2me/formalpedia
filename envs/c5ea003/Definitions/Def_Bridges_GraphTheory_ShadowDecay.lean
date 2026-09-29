-- Prove2me | Definitions.Def_Bridges_GraphTheory_ShadowDecay
-- name    : Bridges_GraphTheory_ShadowDecay
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:35.987614+00:00
-- url     : https://prove2.me/theorems/c24fe10b-ebc2-447f-9bad-f5ba226fad85
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_ShadowDecay
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.ShadowDecay`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/ShadowDecay.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Shadow Decay Profiles for Algebraic Circuit Lower Bounds

This file introduces the **shadow decay profile** as a new complexity invariant
for multivariate polynomials, connecting algebraic circuit complexity to the
combinatorial geometry of polynomial supports.

## Main Definitions

* `ShadowDecay.totalDeg` — Total degree of a multi-index.
* `ShadowDecay.kthShadow` — The k-th downward shadow of a finite support set.
* `ShadowDecay.shadowProfile` — The shadow profile `k ↦ |Shadow_k(S)|`.
* `ShadowDecay.degreeSimplex` — The set of multi-indices with total degree ≤ d.
* `ShadowDecay.circuitShadowEnvelope` — Upper envelope for circuit-bounded supports.
* `ShadowDecay.HasSlowShadowDecay` — Predicate for supports with slow shadow decay.
* `ShadowDecay.elemSymmSupport` — Support of elementary symmetric polynomials.

## Main Results

* `ShadowDecay.kthShadow_subset_degreeSimplex` — Shadows stay inside lower-degree simplices.
* `ShadowDecay.shadowProfile_le_degreeSimplex_card` — Shadow profile bounded by simplex size.
* `ShadowDecay.kthShadow_elemSymm_eq` — Exact shadow characterization for elem. symm. supports.
* `ShadowDecay.shadowProfile_elemSymm` — Exact shadow profile for elementary symmetric supports.

## Cross-Domain Connections

This development bridges:
- **Algebraic complexity theory**: circuit lower bounds via support invariants
- **Extremal combinatorics**: shadow phenomena for set families (Kruskal–Katona)
- **Discrete convex geometry**: Newton polytope contraction under differentiation
- **Geometric complexity theory**: combinatorial front-end to orbit-closure methods
-/

open Finset BigOperators

namespace ShadowDecay

variable {n : ℕ}

/-! ## Total Degree for Multi-indices -/

/-- Total degree of a multi-index `m : Fin n → ℕ`. -/
def totalDeg (m : Fin n → ℕ) : ℕ := ∑ i, m i



/-! ## Degree Simplex -/

/-- The **degree-d simplex**: all multi-indices in `(Fin n → ℕ)` with total degree ≤ d. -/
def degreeSimplex (n d : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (d + 1))).filter
    (fun m => totalDeg m ≤ d)


/-! ## k-th Shadow Definition -/

/-- The **k-th shadow** of a finite set `S` of multi-indices.
`β ∈ kthShadow S k` iff there exists `α ∈ S` with `β ≤ α` (pointwise)
and the total degree drop `∑ᵢ (α i - β i) = k`. -/
def kthShadow (S : Finset (Fin n → ℕ)) (k : ℕ) : Finset (Fin n → ℕ) :=
  S.biUnion (fun α =>
    (degreeSimplex n (totalDeg α)).filter (fun β =>
      (∀ i, β i ≤ α i) ∧ ∑ i, (α i - β i) = k))


/-! ## Basic Shadow Properties -/




/-! ## Shadow Profile -/

/-- The **shadow profile** of a finite support set: the cardinality of the k-th shadow. -/
def shadowProfile (S : Finset (Fin n → ℕ)) (k : ℕ) : ℕ :=
  (kthShadow S k).card


/-! ## Circuit Shadow Envelope -/


/-! ## Slow Shadow Decay Predicate -/


/-! ## Theorem: Shadow Containment in Degree Simplex -/




/-! ## Shadow Profile Monotonicity -/


/-! ## Shadow Profile Subadditivity -/


/-! ## Elementary Symmetric Support -/

/-- The **support of the elementary symmetric polynomial** `e_r(x_1, ..., x_n)`.
This consists of all 0-1 vectors with exactly `r` ones, corresponding to
all `r`-element subsets of `{1, ..., n}`. -/
def elemSymmSupport (n r : ℕ) : Finset (Fin n → ℕ) :=
  ((Finset.univ : Finset (Fin n)).powersetCard r).image
    (fun S i => if i ∈ S then 1 else 0)


/-
The total degree of any element of `elemSymmSupport n r` is `r`.
-/

/-
The cardinality of `elemSymmSupport n r` equals `C(n, r)`.
-/

/-! ## Theorem: Elementary Symmetric Shadow Characterization -/

/-
**The k-th shadow of elementary symmetric support is contained in
the lower-degree elementary symmetric support.**
-/

/-
**Every element of `elemSymmSupport n (r - k)` arises as a shadow element.**
-/



/-! ## Degree Simplex Lattice Point Count -/

/-
The number of lattice points in the degree-d simplex in n variables
equals `Nat.choose (n + d) n` (stars and bars).
-/


end ShadowDecay


