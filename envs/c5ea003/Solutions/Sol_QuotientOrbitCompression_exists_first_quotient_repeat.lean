-- Prove2me | solution 1 for QuotientOrbitCompression.exists_first_quotient_repeat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:40:17.168647+00:00
-- url     : https://prove2.me/submissions/616f587f-d736-43b3-8dea-ed8e0669fc23

-- Sol generated from Bridges/QuotientOrbitCompression/Core.lean
import Mathlib
import Definitions.Def_Bridges_QuotientOrbitCompression_Core
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the project LICENSE file.
-/

/-!
# Quotient Orbit Compression: Core Theory

## Bridge: Algebraic Dynamics ↔ Cryptographic Collision Bounds ↔ EML State Compression

This file develops a theory of **quotient-observable dynamics** for finite iterates.
The central result is that any deterministic trajectory on a finite type `α` must
produce a collision (under a decidable setoid `ρ`) within at most `|α/ρ|` steps.

This simultaneously serves as:
- An **algebraic dynamical system** theorem on finite quotient recurrence,
- An **EML-style observable-state compression** principle,
- A **cryptographic collision certificate** on quotient states,
- A **certified robustness** statement for quotient-observable trajectories.

## Main results

- `quotient_eq_implies_rel`: Quotient equality implies setoid relation.
- `exists_lt_lt_iterate_quotient_eq`: Pigeonhole gives distinct iterates with equal quotient.
- `exists_iterate_rel_of_card_quotient`: Core theorem — bounded-horizon quotient collision.
- `eml_observable_orbit_bound`: Observable orbit count ≤ quotient cardinality.
- `post_quantum_security_collision_upper_bound`: Crypto-facing collision certificate.
- `certified_robustness_via_quotient_compression`: Universal certified robustness.
-/

open Function Finset Fintype

open QuotientOrbitCompression

/-! ## §1. Foundational quotient-relation lemmas -/

/-- **Bridge: quotient algebra → setoid relation.**
    Equality in the quotient `α/ρ` implies the underlying setoid relation `ρ.r`. -/
theorem quotient_eq_implies_rel
    {α : Type*} (ρ : Setoid α) {a b : α} :
    Quotient.mk (s := ρ) a = Quotient.mk (s := ρ) b → ρ.r a b := by
  intro h; exact Quotient.exact h

/-! ## §2. Pigeonhole on quotient traces -/

/-- **Core pigeonhole on quotient traces**: there exist distinct indices `m < n ≤ |α/ρ|`
    such that the quotient images of `f^[m](x)` and `f^[n](x)` coincide.
    Bridge: finite combinatorics → quotient dynamical systems. -/
theorem exists_lt_lt_iterate_quotient_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (ρ : Setoid α) [DecidableRel ρ.r]
    (f : α → α) (x : α) :
    ∃ m n : ℕ, m < n ∧ n ≤ Fintype.card (Quotient ρ) ∧
      Quotient.mk (s := ρ) ((f^[m]) x) = Quotient.mk (s := ρ) ((f^[n]) x) := by
  have hcard : Fintype.card (Quotient ρ) < Fintype.card (Fin (Fintype.card (Quotient ρ) + 1)) := by
    simp [Fintype.card_fin]
  let g : Fin (Fintype.card (Quotient ρ) + 1) → Quotient ρ :=
    fun i => Quotient.mk (s := ρ) ((f^[i.1]) x)
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact ⟨i.1, j.1, h, Nat.le_of_lt_succ j.isLt, heq⟩
  · exact ⟨j.1, i.1, h, Nat.le_of_lt_succ i.isLt, heq.symm⟩

/-- **Core theorem — quotient-cardinality recurrence.**
    For any endomorphism `f` on a finite type `α` with decidable setoid `ρ`,
    every point `x` has iterates `f^[m](x)` and `f^[n](x)` that are `ρ`-related
    with `m < n ≤ |α/ρ|`.

    **Bridge: algebraic dynamics ↔ cryptographic collision bounds.**
    Complexity: O(|α/ρ|) observations suffice for collision detection.

    **Bridge: quotient cardinality ↔ certified robustness observables.** -/
theorem exists_iterate_rel_of_card_quotient
    {α : Type*} [Fintype α] [DecidableEq α]
    (ρ : Setoid α) [DecidableRel ρ.r]
    (f : α → α) (x : α) :
    ∃ m n : ℕ, m < n ∧ n ≤ Fintype.card (Quotient ρ) ∧
      ρ.r ((f^[m]) x) ((f^[n]) x) := by
  obtain ⟨m, n, hmn, hbound, heq⟩ := exists_lt_lt_iterate_quotient_eq ρ f x
  exact ⟨m, n, hmn, hbound, quotient_eq_implies_rel ρ heq⟩

/-! ## §3. Observable orbit definitions and bounds -/






/-! ## §4. Compression statistics -/






/-
**Orbit compression ratio is at most 1**: the quotient never has more states
    than the ambient type. Bridge: information theory → algebraic compression.
-/


/-! ## §5. Cryptographic collision certificates -/





/-! ## §6. First-repeat and certificate structures -/




/-
**Existence of first quotient repeat within the horizon.**
    Upgrades pigeonhole into a genuine orbit-structure theorem with minimality.
    Bridge: orbit structure theory → minimal collision extraction.
-/

/-! ## §7. Setoid-respecting dynamics and semiconjugacy -/


/-
**Iterated stability**: if `f` respects `ρ`, then `f^[n]` respects `ρ` for all `n`.
    Bridge: congruence algebra → iterated dynamical stability.
-/


/-
**Semiconjugacy of iteration**: iteration commutes with quotient projection.
    `(quotientLiftMap ρ f hf)^[n] (⟦x⟧) = ⟦f^[n](x)⟧`

    Bridge: semiring congruence functoriality ↔ quotient dynamical systems.
-/

/-! ## §8. Saturation and exactness -/


/-
**Saturation implies maximal observable count**: the upper bound is tight
    under saturation. Bridge: saturation analysis → sharp compression bounds.
-/

/-! ## §9. Monotonicity of observable orbit count -/

/-
Observable orbit set is monotone in the horizon.
-/


/-
Observable orbit count at step 0 is exactly 1.
-/



/-! ## §10. Concrete models -/



/-
Quotient of `Bool` by discrete setoid has cardinality 2.
-/



/-
`|α/ρ| ≤ |α|` for any setoid.
-/



open QuotientOrbitCompression in
theorem solution    {α : Type*} [Fintype α] [DecidableEq α]
    (ρ : Setoid α) [DecidableRel ρ.r]
    (f : α → α) (x : α) :
    ∃ m n, isFirstQuotientRepeat ρ f x m n ∧ n ≤ Fintype.card (Quotient ρ) := by
  -- Let's denote the set of indices where the quotient repeat occurs as S.
  set S := {n | ∃ m < n, ρ.r ((f^[m]) x) ((f^[n]) x)} with hS_def;
  -- By the well-ordering principle, S has a least element n₀.
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ ∈ S, ∀ n ∈ S, n₀ ≤ n := by
    have h_nonempty : S.Nonempty := by
      exact Exists.elim ( exists_iterate_rel_of_card_quotient ρ f x ) fun m hm => Exists.elim hm fun n hn => ⟨ n, m, hn.1, hn.2.2 ⟩;
    exact ⟨ Nat.find h_nonempty, Nat.find_spec h_nonempty, fun n hn => Nat.find_min' h_nonempty hn ⟩;
  obtain ⟨ ⟨ m, hm₁, hm₂ ⟩, hm₃ ⟩ := hn₀;
  refine' ⟨ m, n₀, ⟨ hm₁, hm₂, _ ⟩, _ ⟩;
  · exact fun a b hab hbn₀ h => not_lt_of_ge ( hm₃ b ⟨ a, hab, h ⟩ ) hbn₀;
  · have := exists_iterate_rel_of_card_quotient ρ f x;
    exact le_trans ( hm₃ _ ⟨ _, this.choose_spec.choose_spec.1, this.choose_spec.choose_spec.2.2 ⟩ ) this.choose_spec.choose_spec.2.1
