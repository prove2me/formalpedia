-- Prove2me | solution 1 for radical_fixpoint_iff_inter_primes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:29:43.388003+00:00
-- url     : https://prove2.me/submissions/8e43475d-7a16-4e85-9aeb-b5f8b5734d14

-- Sol generated from Algebra/ProofSpectra/Core.lean
import Mathlib
import Definitions.Def_Algebra_ProofSpectra_Core
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proof-Theoretic Algebraic Geometry: Prime Congruence Spectra and Idempotent Cut-Elimination

This file founds **proof-theoretic algebraic geometry** by establishing that semiring
congruences carry a rich geometric structure analogous to the Zariski topology on
commutative rings. The central objects are:

- **Prime congruences** on semirings (the analogue of prime ideals)
- **Proof spectra** — the set of prime congruences, forming a spectral-like space
- **Idempotent semirings** — where x + x = x, connecting to tropical geometry
- **Zariski-closed proof varieties** via a Galois connection

## Main results

* `zariskiClosed_iInter` — V(⋃ 𝒮) = ⋂ V(S): closed under arbitrary intersections
* `zariskiClosed_union_eq_inter` — V(S ∪ T) = V(S) ∩ V(T)
* `galois_connection_theory_variety` — The Galois connection S ⊆ Th(X) ↔ X ⊆ V(S)
* `idempotent_add_natural_preorder` — Idempotent addition induces a natural preorder
* `idem_add_is_join` — Addition is the join operation in the natural order
* `prime_cong_zero_class_prime_theory` — Zero-class of prime congruence is a prime theory
* `radical_fixpoint_iff_inter_primes` — Radical = T ↔ T is intersection of primes
* `radicalTheory_idempotent` — The radical operator is idempotent
* `towerExp_ge_pow` — Tower function grows faster than simple exponentiation
* `nontrivial_prime_exists` — Integral domains have non-degenerate prime congruences
* `idem_nsmul_eq` — Summing n copies of x in an idempotent monoid gives x

## Bridge: algebraic_geometry ↔ proof_theory

Proof systems form semirings: disjunction = addition, conjunction = multiplication.
Prime congruences are "geometric points", Zariski-closed sets = provability loci.

## Bridge: tropical_geometry ↔ computational_complexity

Idempotent semirings (x + x = x) are tropical semirings. Every congruence admits
a prime refinement, yielding decidability with explicit complexity bounds.
-/


set_option maxHeartbeats 400000

universe u

open Set

/-! ## Section 1: Semiring Congruences -/


open SRCong

variable {R : Type u} [Semiring R]










/-! ## Section 2: Prime Congruences and the Proof Spectrum -/


open PrimeSRCong

variable {R : Type u} [Semiring R]




/-! ## Section 3: Zariski Closed Sets and the Galois Connection -/














/-! ## Section 4: Theories and Prime Theories -/







/-! ## Section 5: Idempotent Semirings and Natural Order -/













/-! ## Section 6: Radical Congruences and the Nullstellensatz Connection -/


/-- Every theory is contained in its radical.
    Bridge: connects algebraic_geometry to proof_theory via radical containment. -/
theorem subset_radicalTheory {R : Type u} [Semiring R] (T : Set R) :
    T ⊆ radicalTheory T := by
  intro a ha P _ hTP
  exact hTP ha





/-! ## Section 7: Proof Varieties and the Nullstellensatz Galois Connection -/






/-! ## Section 8: Distinguished Congruences -/







/-! ## Section 9: Cut-Elimination Witnesses -/



/-! ## Section 10: Tower Function and Complexity Bounds -/









/-! ## Section 11: Hardness Lower Bounds -/




/-! ## Section 12: Summary Cross-Domain Bridges -/




theorem solution{R : Type u} [Semiring R] {T : Set R} :
    radicalTheory T = T ↔
    T = ⋂₀ {P : Set R | IsPrimeTheory P ∧ T ⊆ P} := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro a ha
      simp only [Set.mem_sInter, Set.mem_setOf_eq]
      intro P ⟨_, hTP⟩
      exact hTP ha
    · intro a ha
      rw [← h]
      intro P hP hTP
      simp only [Set.mem_sInter, Set.mem_setOf_eq] at ha
      exact ha P ⟨hP, hTP⟩
  · intro h
    apply Set.Subset.antisymm
    · intro a ha
      rw [h]
      simp only [Set.mem_sInter, Set.mem_setOf_eq]
      intro P ⟨hP, hTP⟩
      exact ha P hP hTP
    · exact subset_radicalTheory T
