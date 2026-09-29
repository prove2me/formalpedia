-- Prove2me | solution 1 for mme_CW_q6_primary_hash_bucket_fixed_z_membership
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:15:12.687487+00:00
-- url     : https://prove2.me/submissions/e3b96f3d-d67d-444b-a9ff-894385c39ab4

import Mathlib
import Definitions.Def_mme_CW_q6_primary_hash_bucket
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity

open BigOperators MME

set_option autoImplicit false

/-- Pointwise membership in the literal q=6 bucket is the conjunction of
the X-minus-Z difference equation and retention of the common Z label. -/
theorem solution
    (N L G Xcount : ℕ)
    (S : Finset ℕ)
    (b0 : ZMod (4 * Xcount ^ 2 + 1))
    (w : Fin (2 * N) → ZMod (4 * Xcount ^ 2 + 1))
    (e : CWQ6ExactCoupledAddress N L G) :
    e ∈ cwQ6PrimaryHashBucket N L G Xcount S b0 w ↔
      (∑ j,
        ((2 * ((e.1 0 j).val : ZMod (4 * Xcount ^ 2 + 1))) -
          (cwQ6CoupledZHashCode (e.1 2 j) :
            ZMod (4 * Xcount ^ 2 + 1))) * w j) = 0 ∧
      ∃ s ∈ S,
        cwQ6DoubledZHash b0 w (e.1 2) =
          2 * (s : ZMod (4 * Xcount ^ 2 + 1)) := by
  classical
  let M := 4 * Xcount ^ 2 + 1
  have hsupp : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress e.1 e.1 e.1) := by
    simpa [cwQ6CoupledMixedAddress] using e.2.1
  have hap := mme_CW_q6_doubled_hash_AP_identity b0 w e.1 e.1 e.1 hsupp
  have hdiff :
      cwQ6DoubledXHash b0 w (e.1 0) -
          cwQ6DoubledZHash b0 w (e.1 2) =
        ∑ j,
          ((2 * ((e.1 0 j).val : ZMod M)) -
            (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) * w j := by
    simp only [cwQ6DoubledXHash, cwQ6DoubledZHash]
    have hterm :
        (∑ j,
          ((2 * ((e.1 0 j).val : ZMod M)) -
            (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) * w j) =
          (∑ j, (2 * ((e.1 0 j).val : ZMod M)) * w j) -
            ∑ j, (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M) * w j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hterm]
    norm_cast
    ring
  constructor
  · intro he
    simp only [cwQ6PrimaryHashBucket, Finset.mem_filter,
      Finset.mem_univ, true_and] at he
    obtain ⟨s, hs, hx, hy, hz⟩ := he
    refine ⟨?_, ⟨s, hs, hz⟩⟩
    rw [← hdiff]
    rw [hx, hz]
    ring
  · rintro ⟨hdiffzero, s, hs, hz⟩
    have hxz : cwQ6DoubledXHash b0 w (e.1 0) =
        cwQ6DoubledZHash b0 w (e.1 2) := by
      have : cwQ6DoubledXHash b0 w (e.1 0) -
          cwQ6DoubledZHash b0 w (e.1 2) = 0 := by
        rw [hdiff]
        exact hdiffzero
      exact sub_eq_zero.mp this
    have hyz : cwQ6DoubledYHash b0 w (e.1 1) =
        cwQ6DoubledZHash b0 w (e.1 2) := by
      rw [hxz] at hap
      linear_combination hap
    simp only [cwQ6PrimaryHashBucket, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨s, hs, hxz.trans hz, hyz.trans hz, hz⟩
