-- Prove2me | solution 1 for mme_CW_q6_regular_primary_hash_bucket_weighted_isolated_many_z_stars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T01:29:51.818197+00:00
-- url     : https://prove2.me/submissions/d67c3ff4-3ca1-493a-9d39-54eaa339f796

import Mathlib
import Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_ordered_collision_sum_le
import Theorems.Thm_mme_CW_q6_primary_hash_bucket_fixed_z_membership
import Theorems.Thm_mme_finite_weighted_collision_budget_retains_fibers
import Theorems.Thm_mme_CW_q6_retained_z_star_parameter_sum_lower_tail_gap

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A concrete same-parameter q=6 wrapper: an arbitrary-gap Z-star moment,
the exact regular-bucket X/Y collision moment, and weighted deterministic
pruning produce a literal bucket with many large shared Z-fibers. -/
theorem solution
    {n L G K H R Q : ℕ}
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (hG : 0 < G)
    (hHK : H ≤ K) (hR : 0 < R)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1))
    (hgap :
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1) * K + R ≤
        Nat.choose (2 * G) G)
    (harith :
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ^ (2 * n + 3) *
            ((K - H + 1) * R ^ 2 * Q) +
          R ^ 2 *
            (2 *
                ((cwQ6ExactZWords (n + 1) L G).card *
                  Nat.choose (2 * G) G) *
              (Nat.choose (n + 1) G) ^ 2 * S.card *
              (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ^ (2 * n)) +
          (K - H + 1) *
            (2 * Nat.choose (2 * G) G *
              (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ^ (2 * n + 3) *
              S.card * (cwQ6ExactZWords (n + 1) L G).card) ≤
        (K - H + 1) *
          (R ^ 2 *
            (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ^ (2 * n + 2) *
            S.card * (cwQ6ExactZWords (n + 1) L G).card)) :
    ∃ w : Fin (2 * n + 2) →
          ZMod (4 * (Nat.choose (n + 1) G) ^ 2 + 1),
      ∃ b0 : ZMod (4 * (Nat.choose (n + 1) G) ^ 2 + 1),
        ∃ I : Finset (CWQ6ExactCoupledAddress (n + 1) L G),
          I ⊆ cwQ6PrimaryHashBucket (n + 1) L G
              (Nat.choose (n + 1) G) S b0 w ∧
          (∀ e ∈ I,
            ∀ e' ∈ cwQ6PrimaryHashBucket (n + 1) L G
                (Nat.choose (n + 1) G) S b0 w,
              (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
          Q ≤ ((cwQ6ExactZWords (n + 1) L G).filter (fun z =>
            H ≤ (I.filter (fun e => e.1 2 = z)).card)).card := by
  classical
  let X : ℕ := Nat.choose (n + 1) G
  let B : ℕ := Nat.choose (2 * G) G
  let M : ℕ := 4 * X ^ 2 + 1
  let Z : Finset (Fin (2 * (n + 1)) → Fin 3) :=
    cwQ6ExactZWords (n + 1) L G
  have hXwordsPos : 0 < (cwQ6ExactXWords (n + 1) L G).card := by
    rw [hregular.x_word_card]
    exact Nat.choose_pos (by omega)
  obtain ⟨xword, hxword⟩ := Finset.card_pos.mp hXwordsPos
  obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hxword
  have hxfiberPos :
      0 < ((cwQ6ExactAddresses (n + 1) L G).filter
        (fun e => e 0 = xword)).card := by
    apply Finset.card_pos.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
    exact hax
  rw [hregular.x_degree xword hxword] at hxfiberPos
  have hX : 0 < X := by
    by_contra hnot
    have hxzero : X = 0 := Nat.eq_zero_of_not_pos hnot
    simp [X, hxzero] at hxfiberPos
  have hMpos : 0 < M := by
    dsimp [M]
    omega
  letI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  have hM : 2 < M := by
    dsimp [M]
    have hxone : 1 ≤ X := hX
    nlinarith [sq_nonneg (X : ℤ)]
  have hodd : Odd M := by
    refine ⟨2 * X ^ 2, ?_⟩
    dsimp [M]
    ring
  have h2 : IsUnit (2 : ZMod M) := by
    change IsUnit ((2 : ℕ) : ZMod M)
    rw [ZMod.isUnit_iff_coprime]
    exact hodd.coprime_two_left
  letI : Fintype (CWQ6CoupledAddress (n + 1)) :=
    inferInstanceAs (Fintype (Fin 3 → Fin (2 * (n + 1)) → Fin 3))
  letI : Fintype (CWQ6ExactCoupledAddress (n + 1) L G) :=
    Fintype.ofInjective (fun e => e.1) Subtype.val_injective
  let A : (Fin (2 * (n + 1)) → Fin 3) →
      Finset (CWQ6ExactCoupledAddress (n + 1) L G) := fun z =>
    Finset.univ.filter (fun e => e.1 2 = z)
  have hzA : ∀ z ∈ Z, ∀ e ∈ A z, e.1 2 = z := by
    intro z hz e he
    exact (Finset.mem_filter.mp he).2
  have hAcard : ∀ z ∈ Z, (A z).card = B := by
    intro z hz
    let Fraw := (cwQ6ExactAddresses (n + 1) L G).filter
      (fun e => e 2 = z)
    have himage : (A z).image (fun e => e.1) = Fraw := by
      ext a
      constructor
      · intro ha'
        obtain ⟨e, heA, rfl⟩ := Finset.mem_image.mp ha'
        have hez := (Finset.mem_filter.mp heA).2
        have heExact : e.1 ∈ cwQ6ExactAddresses (n + 1) L G := by
          simp only [cwQ6ExactAddresses, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact e.2
        exact Finset.mem_filter.mpr ⟨heExact, hez⟩
      · intro ha'
        have ha'' := Finset.mem_filter.mp ha'
        have hexact := ha''.1
        have hprops :
            CWQ6CoupledCoordinatewiseSupported a ∧
              ∀ i r : Fin 3,
                (Finset.univ.filter
                  (fun j : Fin (2 * (n + 1)) => a i j = r)).card =
                    cwQ6CoupledMarginalMultiplicity (n + 1) L G i r := by
          simpa only [cwQ6ExactAddresses, Finset.mem_filter,
            Finset.mem_univ, true_and] using hexact
        let e : CWQ6ExactCoupledAddress (n + 1) L G := ⟨a, hprops⟩
        apply Finset.mem_image.mpr
        refine ⟨e, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha''.2⟩
    calc
      (A z).card = ((A z).image (fun e => e.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = Fraw.card := congrArg Finset.card himage
      _ = B := by
        simpa only [Fraw, B, Z] using hregular.z_degree z hz
  let degree :
      (Fin (2 * (n + 1)) → Fin 3) →
        (Fin (2 * n + 2) → ZMod M) → ℕ := fun z w =>
    ((A z).attach.filter (fun e =>
      ∑ i,
        ((2 * ((e.1.1 0 i).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * w i = 0)).card
  let Ω := (Fin (2 * n + 2) → ZMod M) × ZMod M
  let E : Ω → Finset (CWQ6ExactCoupledAddress (n + 1) L G) := fun ω =>
    cwQ6PrimaryHashBucket (n + 1) L G X S ω.2 ω.1
  let Good : Ω → Finset (Fin (2 * (n + 1)) → Fin 3) := fun ω =>
    Z.filter (fun z =>
      K ≤ degree z ω.1 ∧
        ∃ s ∈ S,
          cwQ6DoubledZHash ω.2 ω.1 z = 2 * (s : ZMod M))
  let collision : Ω → ℕ := fun ω =>
    (((E ω).product (E ω)).filter (fun p =>
      p.1 ≠ p.2 ∧
        (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))).card
  have hstar :=
    mme_CW_q6_retained_z_star_parameter_sum_lower_tail_gap
      hM h2 hG Z A hzA hAcard
        (by simpa only [M, B] using hgap) S
        (by simpa only [M, X] using hSrange)
  change
    R ^ 2 * M ^ (2 * n + 2) * S.card * Z.card ≤
      R ^ 2 * (∑ ω : Ω, (Good ω).card) +
        2 * B * M ^ (2 * n + 3) * S.card * Z.card at hstar
  have hcollision :=
    mme_CW_q6_regular_primary_hash_bucket_ordered_collision_sum_le
      hregular S (by simpa only [X, M] using hSrange)
  have hZcard :
      Z.card = Nat.choose (2 * (n + 1)) L *
        Nat.choose (2 * (n + 1) - L) L := by
    simpa only [Z] using hregular.z_word_card
  rw [← hZcard] at hcollision
  change
    (∑ ω : Ω, collision ω) ≤
      2 * (Z.card * B) * X ^ 2 * S.card * M ^ (2 * n) at hcollision
  have hΩcard : Fintype.card Ω = M ^ (2 * n + 3) := by
    dsimp only [Ω]
    rw [Fintype.card_prod]
    rw [show Fintype.card (Fin (2 * n + 2) → ZMod M) =
      M ^ (2 * n + 2) by simp]
    rw [show Fintype.card (ZMod M) = M by simp]
    rw [← pow_succ]
  change
    M ^ (2 * n + 3) * ((K - H + 1) * R ^ 2 * Q) +
          R ^ 2 * (2 * (Z.card * B) * X ^ 2 * S.card * M ^ (2 * n)) +
          (K - H + 1) *
            (2 * B * M ^ (2 * n + 3) * S.card * Z.card) ≤
      (K - H + 1) *
        (R ^ 2 * M ^ (2 * n + 2) * S.card * Z.card) at harith
  have harithActual :
      M ^ (2 * n + 3) * ((K - H + 1) * R ^ 2 * Q) +
            R ^ 2 * (∑ ω : Ω, collision ω) +
            (K - H + 1) *
              (2 * B * M ^ (2 * n + 3) * S.card * Z.card) ≤
        (K - H + 1) *
          (R ^ 2 * M ^ (2 * n + 2) * S.card * Z.card) := by
    exact harith.trans' (by gcongr)
  have hstarScaled := Nat.mul_le_mul_left (K - H + 1) hstar
  have hwithTail :
      (M ^ (2 * n + 3) * ((K - H + 1) * R ^ 2 * Q) +
          R ^ 2 * (∑ ω : Ω, collision ω)) +
            (K - H + 1) *
              (2 * B * M ^ (2 * n + 3) * S.card * Z.card) ≤
        ((K - H + 1) * R ^ 2 * (∑ ω : Ω, (Good ω).card)) +
            (K - H + 1) *
              (2 * B * M ^ (2 * n + 3) * S.card * Z.card) := by
    calc
      _ ≤ (K - H + 1) *
          (R ^ 2 * M ^ (2 * n + 2) * S.card * Z.card) := harithActual
      _ ≤ (K - H + 1) *
          (R ^ 2 * (∑ ω : Ω, (Good ω).card) +
            2 * B * M ^ (2 * n + 3) * S.card * Z.card) := hstarScaled
      _ = _ := by ring
  have hbudgetNat :
      M ^ (2 * n + 3) * ((K - H + 1) * R ^ 2 * Q) +
          R ^ 2 * (∑ ω : Ω, collision ω) ≤
        (K - H + 1) * R ^ 2 * (∑ ω : Ω, (Good ω).card) :=
    Nat.le_of_add_le_add_right hwithTail
  have hdegree : ∀ ω : Ω, ∀ z ∈ Good ω,
      K ≤ ((E ω).filter (fun e => e.1 2 = z)).card := by
    intro ω z hzGood
    have hzparts := Finset.mem_filter.mp hzGood
    have hdeg := hzparts.2.1
    have hlabel := hzparts.2.2
    let F := (A z).attach.filter (fun e =>
      ∑ i,
        ((2 * ((e.1.1 0 i).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * ω.1 i = 0)
    let I0 := F.image (fun e => e.1)
    have hcardFI : F.card = I0.card := by
      exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
    have hI0E : I0 ⊆ (E ω).filter (fun e => e.1 2 = z) := by
      intro e heI
      obtain ⟨e', heF, rfl⟩ := Finset.mem_image.mp heI
      have heDiff := (Finset.mem_filter.mp heF).2
      have heA := e'.2
      have hez : e'.1.1 2 = z := hzA z hzparts.1 e'.1 heA
      apply Finset.mem_filter.mpr
      refine ⟨?_, hez⟩
      apply (mme_CW_q6_primary_hash_bucket_fixed_z_membership
        (n + 1) L G X S ω.2 ω.1 e'.1).2
      refine ⟨?_, ?_⟩
      · simpa only [M] using heDiff
      · simpa only [hez, M] using hlabel
    have hdegreeCard : degree z ω.1 = F.card := by rfl
    rw [hdegreeCard, hcardFI] at hdeg
    exact hdeg.trans (Finset.card_le_card hI0E)
  have hbudget :
      Fintype.card Ω * ((K - H + 1) * R ^ 2 * Q) +
          R ^ 2 * ∑ ω : Ω, collision ω ≤
        (K - H + 1) * R ^ 2 * ∑ ω : Ω, (Good ω).card := by
    rw [hΩcard]
    exact hbudgetNat
  obtain ⟨ω, I, hIE, hisolated, hretained⟩ :=
    mme_finite_weighted_collision_budget_retains_fibers
      E (fun e => e.1 0) (fun e => e.1 1) (fun e => e.1 2)
      Good K H Q (R ^ 2) hHK (by positivity) hdegree
      (by simpa only [collision] using hbudget)
  have hretainedSubset :
      (Good ω).filter (fun z =>
          H ≤ (I.filter (fun e => e.1 2 = z)).card) ⊆
        Z.filter (fun z =>
          H ≤ (I.filter (fun e => e.1 2 = z)).card) := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz'.1).1, hz'.2⟩
  refine ⟨ω.1, ω.2, I, ?_, ?_, ?_⟩
  · simpa only [E, X] using hIE
  · simpa only [E, X] using hisolated
  · change Q ≤ (Z.filter (fun z =>
      H ≤ (I.filter (fun e => e.1 2 = z)).card)).card
    exact hretained.trans (Finset.card_le_card hretainedSubset)

