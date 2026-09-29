-- Prove2me | solution 1 for mme_complete_split_exact_power_six_finite_common_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T14:32:44.975531+00:00
-- url     : https://prove2.me/submissions/63977572-3ed1-469e-9109-4aab698b1812

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_complete_split_exact_power_six_finite_witness_power

open MME MME.CompleteSplit MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open BigOperators
open scoped NNReal

universe u w

set_option autoImplicit false

/-!
# A common physical length for a finite family of exact complete-profile powers

Each member supplies witnesses only along its own cofinal set of multiplicities. Taking the product
of one witness length per member gives a single `L₀` such that every member has a witness at every
common length `L₀ * r`, which is what a Kronecker product across the family needs.
-/

theorem solution
    {K : Type u} [Field K] {J : Type w} [Fintype J]
    (T : J → TensorObj K 3) {ι : J → Fin 3 → Type u} {ell : J → ℕ}
    (b : (j : J) → (i : Fin 3) → Basis (ι j i) K ((T j).V i))
    (label : (j : J) → (i : Fin 3) → ι j i → CompleteWord (ell j))
    (beta : (j : J) → Fin 3 → Profile (ell j))
    (len : J → ℕ) (hlen : ∀ j, 0 < len j)
    (tau : ℝ) (V v : J → ℝ)
    (hpos : ∀ j, 0 < v j) (hstrict : ∀ j, v j < V j)
    (hvalue : ∀ j, HasSixSequenceRate TensorObj.Restrict
      (fun m ↦ restrictedPower (T j) (b j) (label j) (beta j) 0 (len j * m))
      (fun m ↦ len j * m) tau (V j)) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ (r : ℕ) (j : J),
      len j ∣ L₀ * r ∧
      SixFiniteWitness TensorObj.Restrict
        (restrictedPower (T j) (b j) (label j) (beta j) 0 (L₀ * r)) (L₀ * r) tau (v j) := by
  classical
  have hlocal : ∀ j : J, ∃ m : ℕ,
      1 ≤ m ∧ 1 ≤ len j * m ∧
      SixFiniteWitness TensorObj.Restrict
        (restrictedPower (T j) (b j) (label j) (beta j) 0 (len j * m))
        (len j * m) tau (v j) := by
    intro j
    exact (hvalue j).2 (v j) (hpos j) (hstrict j) 1
  choose m _hm hlength hwitness using hlocal
  let N : J → ℕ := fun j ↦ len j * m j
  let L₀ := ∏ j, N j
  have hL₀ : 0 < L₀ := by
    apply Finset.prod_pos
    intro j _
    exact lt_of_lt_of_le Nat.zero_lt_one (hlength j)
  refine ⟨L₀, hL₀, ?_⟩
  intro r j
  have hdiv : N j ∣ L₀ := Finset.dvd_prod_of_mem N (Finset.mem_univ j)
  obtain ⟨s, hs⟩ := hdiv
  have hphysical : N j * (s * r) = L₀ * r := by
    rw [hs]
    ring
  refine ⟨?_, ?_⟩
  · refine ⟨m j * (s * r), ?_⟩
    calc
      L₀ * r = N j * (s * r) := hphysical.symm
      _ = len j * (m j * (s * r)) := by
        change len j * m j * (s * r) = _
        ring
  · have hnew := mme_complete_split_exact_power_six_finite_witness_power
      (T j) (b j) (label j) (beta j) (N j) (s * r) tau (v j) (hwitness j)
    rw [hphysical] at hnew
    exact hnew
