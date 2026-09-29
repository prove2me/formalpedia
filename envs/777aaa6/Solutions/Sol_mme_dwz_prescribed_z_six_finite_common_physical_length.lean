-- Prove2me | solution 1 for mme_dwz_prescribed_z_six_finite_common_physical_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T07:18:08.922251+00:00
-- url     : https://prove2.me/submissions/a7063cb3-fe09-487c-8b6a-11ea7b2c40b8

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_dwz_prescribed_z_six_finite_restriction_witness_power

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module BigOperators

universe u w

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {J : Type w} [Fintype J]
    (T : J → TensorObj K 3) {ι : J → Type u} {t : J → ℕ}
    (bZ : (i : J) → Basis (ι i) K ((T i).V 2))
    (grade : (i : J) → ι i → Fin (t i))
    (p : (i : J) → IntegerZSplitProfile (t i))
    (tau : ℝ) (V v : J → ℝ)
    (hpos : ∀ i, 0 < v i) (hstrict : ∀ i, v i < V i)
    (hvalue : ∀ i, HasPrescribedZSixRestrictionValueAtLeast
      (T i) (bZ i) (grade i) (p i) tau (V i)) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ (r : ℕ) (i : J), ∃ m : ℕ,
      (p i).length m = L₀ * r ∧
      SixFiniteWitness TensorObj.Restrict
        (prescribedZPower (T i) (bZ i) (grade i) (p i) m)
        (L₀ * r) tau (v i) := by
  classical
  have hlocal : ∀ i : J, ∃ m : ℕ,
      1 ≤ m ∧ 1 ≤ (p i).length m ∧
      SixFiniteWitness TensorObj.Restrict
        (prescribedZPower (T i) (bZ i) (grade i) (p i) m)
        ((p i).length m) tau (v i) := by
    intro i
    exact (hvalue i).2 (v i) (hpos i) (hstrict i) 1
  choose m _hm hlength hwitness using hlocal
  let N : J → ℕ := fun i ↦ (p i).length (m i)
  let L₀ := ∏ i, N i
  have hL₀ : 0 < L₀ := by
    apply Finset.prod_pos
    intro i _
    exact lt_of_lt_of_le Nat.zero_lt_one (hlength i)
  refine ⟨L₀, hL₀, ?_⟩
  intro r i
  have hdiv : N i ∣ L₀ := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  obtain ⟨s, hs⟩ := hdiv
  let m' := m i * (s * r)
  have hphysical : (p i).length m' = L₀ * r := by
    change (p i).denominator * (m i * (s * r)) = L₀ * r
    rw [hs]
    change (p i).denominator * (m i * (s * r)) =
      (((p i).denominator * m i) * s) * r
    ac_rfl
  refine ⟨m', hphysical, ?_⟩
  have hnew := mme_dwz_prescribed_z_six_finite_restriction_witness_power
    (T i) (bZ i) (grade i) (p i) (m i) (s * r) tau (v i) (hwitness i)
  change SixFiniteWitness TensorObj.Restrict
    (prescribedZPower (T i) (bZ i) (grade i) (p i) m')
    ((p i).length m') tau (v i) at hnew
  rw [hphysical] at hnew
  exact hnew
