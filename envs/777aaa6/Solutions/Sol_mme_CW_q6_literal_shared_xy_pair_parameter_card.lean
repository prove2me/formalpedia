-- Prove2me | solution 1 for mme_CW_q6_literal_shared_xy_pair_parameter_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:24:36.174509+00:00
-- url     : https://prove2.me/submissions/8de4dcf2-598e-4962-a0a0-8383693cedb5

import Mathlib
import Theorems.Thm_mme_CW_q6_shared_xy_pair_hash_parameter_card
import Theorems.Thm_mme_CW_q6_primary_hash_bucket_fixed_z_membership
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable local instance q6LiteralPairSolutionExactAddressDecidableEq
    (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) :=
  Classical.decEq _

/-- A fixed distinct pair sharing X or Y belongs simultaneously to the
literal q=6 bucket for exactly `|S| M^(2n)` affine parameters. -/
theorem solution
    {n L G Xcount : ℕ}
    (e f : CWQ6ExactCoupledAddress (n + 1) L G)
    (hne : e ≠ f)
    (hshare : e.1 0 = f.1 0 ∨ e.1 1 = f.1 1)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (4 * Xcount ^ 2 + 1)) :
    (((Finset.univ : Finset
        ((Fin (2 * n + 2) → ZMod (4 * Xcount ^ 2 + 1)) ×
          ZMod (4 * Xcount ^ 2 + 1))).filter (fun ω :
            (Fin (2 * n + 2) → ZMod (4 * Xcount ^ 2 + 1)) ×
              ZMod (4 * Xcount ^ 2 + 1) =>
      e ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1 ∧
      f ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1)).card) =
        S.card * (4 * Xcount ^ 2 + 1) ^ (2 * n) := by
  classical
  let M : ℕ := 4 * Xcount ^ 2 + 1
  let c : CWQ6ExactCoupledAddress (n + 1) L G →
      Fin (2 * n + 2) → ZMod M := fun a j =>
    (2 * ((a.1 0 j).val : ZMod M)) -
      (cwQ6CoupledZHashCode (a.1 2 j) : ZMod M)
  have hodd : Odd M := by
    refine ⟨2 * Xcount ^ 2, ?_⟩
    dsimp [M]
    ring
  have h2 : IsUnit (2 : ZMod M) := by
    change IsUnit ((2 : ℕ) : ZMod M)
    rw [ZMod.isUnit_iff_coprime]
    exact hodd.coprime_two_left
  have hXZ (a : CWQ6ExactCoupledAddress (n + 1) L G)
      (w : Fin (2 * n + 2) → ZMod M) (b0 : ZMod M)
      (ha : ∑ i, c a i * w i = 0) :
      cwQ6DoubledXHash b0 w (a.1 0) =
        cwQ6DoubledZHash b0 w (a.1 2) := by
    have ha' := ha
    simp only [c, sub_mul] at ha'
    rw [Finset.sum_sub_distrib] at ha'
    have hsum :
        (∑ i, 2 * ((a.1 0 i).val : ZMod M) * w i) =
          ∑ i, (cwQ6CoupledZHashCode (a.1 2 i) : ZMod M) * w i :=
      sub_eq_zero.mp ha'
    simp only [cwQ6DoubledXHash, cwQ6DoubledZHash, Nat.cast_mul,
      Nat.cast_ofNat]
    rw [hsum]
  have hYZ (a : CWQ6ExactCoupledAddress (n + 1) L G)
      (w : Fin (2 * n + 2) → ZMod M) (b0 : ZMod M)
      (ha : ∑ i, c a i * w i = 0) :
      cwQ6DoubledYHash b0 w (a.1 1) =
        cwQ6DoubledZHash b0 w (a.1 2) := by
    have hsupp : CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress a.1 a.1 a.1) := by
      intro j
      simpa [cwQ6CoupledMixedAddress] using a.2.1 j
    have hap := mme_CW_q6_doubled_hash_AP_identity
      b0 w a.1 a.1 a.1 hsupp
    rw [hXZ a w b0 ha] at hap
    have hap' :
        cwQ6DoubledZHash b0 w (a.1 2) +
            cwQ6DoubledYHash b0 w (a.1 1) =
          cwQ6DoubledZHash b0 w (a.1 2) +
            cwQ6DoubledZHash b0 w (a.1 2) := by
      simpa only [two_mul] using hap
    exact add_left_cancel hap'
  have hEvent (ω :
      (Fin (2 * n + 2) → ZMod M) × ZMod M) :
      (e ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1 ∧
        f ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1) ↔
      ((∑ i, c e i * ω.1 i = 0) ∧
        (∑ i, c f i * ω.1 i = 0) ∧
        ∃ s ∈ S,
          cwQ6DoubledZHash ω.2 ω.1 (e.1 2) = 2 * (s : ZMod M)) := by
    have heMem := mme_CW_q6_primary_hash_bucket_fixed_z_membership
      (n + 1) L G Xcount S ω.2 ω.1 e
    have hfMem := mme_CW_q6_primary_hash_bucket_fixed_z_membership
      (n + 1) L G Xcount S ω.2 ω.1 f
    change (e ∈ _ ∧ f ∈ _) ↔ _
    constructor
    · rintro ⟨he, hf⟩
      have he' := heMem.mp he
      have hf' := hfMem.mp hf
      exact ⟨he'.1, hf'.1, he'.2⟩
    · rintro ⟨heq, hfeq, hlabel⟩
      have hzeq :
          cwQ6DoubledZHash ω.2 ω.1 (e.1 2) =
            cwQ6DoubledZHash ω.2 ω.1 (f.1 2) := by
        rcases hshare with hx | hy
        · calc
            cwQ6DoubledZHash ω.2 ω.1 (e.1 2) =
                cwQ6DoubledXHash ω.2 ω.1 (e.1 0) :=
              (hXZ e ω.1 ω.2 heq).symm
            _ = cwQ6DoubledXHash ω.2 ω.1 (f.1 0) := by rw [hx]
            _ = cwQ6DoubledZHash ω.2 ω.1 (f.1 2) := hXZ f ω.1 ω.2 hfeq
        · calc
            cwQ6DoubledZHash ω.2 ω.1 (e.1 2) =
                cwQ6DoubledYHash ω.2 ω.1 (e.1 1) :=
              (hYZ e ω.1 ω.2 heq).symm
            _ = cwQ6DoubledYHash ω.2 ω.1 (f.1 1) := by rw [hy]
            _ = cwQ6DoubledZHash ω.2 ω.1 (f.1 2) := hYZ f ω.1 ω.2 hfeq
      have hlabelF : ∃ s ∈ S,
          cwQ6DoubledZHash ω.2 ω.1 (f.1 2) = 2 * (s : ZMod M) := by
        obtain ⟨s, hs, hsval⟩ := hlabel
        exact ⟨s, hs, hzeq ▸ hsval⟩
      exact ⟨heMem.mpr ⟨heq, hlabel⟩, hfMem.mpr ⟨hfeq, hlabelF⟩⟩
  let Literal : Finset
      ((Fin (2 * n + 2) → ZMod M) × ZMod M) :=
    Finset.univ.filter (fun ω =>
      e ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1 ∧
      f ∈ cwQ6PrimaryHashBucket (n + 1) L G Xcount S ω.2 ω.1)
  let Event : Finset
      ((Fin (2 * n + 2) → ZMod M) × ZMod M) :=
    Finset.univ.filter (fun ω =>
      (∑ i, c e i * ω.1 i = 0) ∧
      (∑ i, c f i * ω.1 i = 0) ∧
      ∃ s ∈ S,
        cwQ6DoubledZHash ω.2 ω.1 (e.1 2) = 2 * (s : ZMod M))
  have hsets : Literal = Event := by
    ext ω
    simp only [Literal, Event, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hEvent ω
  have hcount := mme_CW_q6_shared_xy_pair_hash_parameter_card
    (M := M) h2 e f hne hshare S (by simpa [M] using hSrange)
  change Event.card = S.card * M ^ (2 * n) at hcount
  change Literal.card = S.card * M ^ (2 * n)
  rw [hsets]
  exact hcount
