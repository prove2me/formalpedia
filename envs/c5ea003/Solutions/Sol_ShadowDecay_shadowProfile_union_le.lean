-- Prove2me | solution 1 for ShadowDecay.shadowProfile_union_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:42:09.601012+00:00
-- url     : https://prove2.me/submissions/544160b7-29fa-4e47-a2e8-0cd0568d9ca9

-- Sol generated from Bridges/GraphTheory/ShadowDecay.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_ShadowDecay
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

open ShadowDecay

variable {n : ℕ}

/-! ## Total Degree for Multi-indices -/


theorem totalDeg_le_of_le {m₁ m₂ : Fin n → ℕ} (h : ∀ i, m₁ i ≤ m₂ i) :
    totalDeg m₁ ≤ totalDeg m₂ :=
  Finset.sum_le_sum fun i _ => h i


/-! ## Degree Simplex -/


theorem mem_degreeSimplex_iff {n d : ℕ} {m : Fin n → ℕ} :
    m ∈ degreeSimplex n d ↔ totalDeg m ≤ d := by
  simp only [degreeSimplex, mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun ⟨_, h2⟩ => h2
  · intro h
    refine ⟨fun i => ?_, h⟩
    simp only [mem_range]
    have : m i ≤ totalDeg m :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)
    omega

/-! ## k-th Shadow Definition -/


theorem mem_kthShadow_iff {S : Finset (Fin n → ℕ)} {k : ℕ} {β : Fin n → ℕ} :
    β ∈ kthShadow S k ↔ ∃ α ∈ S, (∀ i, β i ≤ α i) ∧ ∑ i, (α i - β i) = k := by
  simp only [kthShadow, mem_biUnion, mem_filter]
  constructor
  · rintro ⟨α, hα, _, hle, hsum⟩
    exact ⟨α, hα, hle, hsum⟩
  · rintro ⟨α, hα, hle, hsum⟩
    refine ⟨α, hα, ?_, hle, hsum⟩
    rw [mem_degreeSimplex_iff]
    exact totalDeg_le_of_le hle

/-! ## Basic Shadow Properties -/




/-! ## Shadow Profile -/



/-! ## Circuit Shadow Envelope -/


/-! ## Slow Shadow Decay Predicate -/


/-! ## Theorem: Shadow Containment in Degree Simplex -/




/-! ## Shadow Profile Monotonicity -/


/-! ## Shadow Profile Subadditivity -/


/-! ## Elementary Symmetric Support -/



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



open ShadowDecay in
theorem solution(S₁ S₂ : Finset (Fin n → ℕ)) (k : ℕ) :
    shadowProfile (S₁ ∪ S₂) k ≤ shadowProfile S₁ k + shadowProfile S₂ k := by
  unfold shadowProfile
  have hsub : kthShadow (S₁ ∪ S₂) k ⊆ kthShadow S₁ k ∪ kthShadow S₂ k := by
    intro β hβ
    rw [mem_kthShadow_iff] at hβ
    obtain ⟨α, hα, hle, hsum⟩ := hβ
    rw [Finset.mem_union] at hα
    rw [Finset.mem_union]
    cases hα with
    | inl h => left; rw [mem_kthShadow_iff]; exact ⟨α, h, hle, hsum⟩
    | inr h => right; rw [mem_kthShadow_iff]; exact ⟨α, h, hle, hsum⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
