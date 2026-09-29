-- Prove2me | solution 1 for mme_CW_q6_regular_primary_hash_bucket_many_z_stars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:26:36.350641+00:00
-- url     : https://prove2.me/submissions/f1b708de-728f-44f2-a961-efac1cab62ce

import Mathlib
import Theorems.Thm_mme_CW_q6_many_retained_z_stars_from_fixed_fiber_moments
import Theorems.Thm_mme_CW_q6_primary_hash_bucket_fixed_z_membership
import Definitions.Def_mme_CW_q6_exact_address_incidence

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The regular exact q=6 profile has one literal affine bucket containing
many Z-fibers above the common half-mean threshold. -/
theorem solution
    {n L G Xcount H : ℕ}
    (hX : 0 < Xcount) (hG : 0 < G)
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (hH : 2 * (4 * Xcount ^ 2 + 1) * H ≤ Nat.choose (2 * G) G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range ((4 * Xcount ^ 2 + 1) / 2)) :
    ∃ w : Fin (2 * n + 2) → ZMod (4 * Xcount ^ 2 + 1),
      ∃ b0 : ZMod (4 * Xcount ^ 2 + 1),
        Nat.choose (2 * G) G * S.card *
              (Nat.choose (2 * (n + 1)) L *
                Nat.choose (2 * (n + 1) - L) L) ≤
          4 * (4 * Xcount ^ 2 + 1) *
              (2 * (4 * Xcount ^ 2 + 1) + Nat.choose (2 * G) G) *
            ((cwQ6ExactZWords (n + 1) L G).filter (fun z =>
              H ≤ ((cwQ6PrimaryHashBucket
                (n + 1) L G Xcount S b0 w).filter
                  (fun e => e.1 2 = z)).card)).card := by
  classical
  let M : ℕ := 4 * Xcount ^ 2 + 1
  let B : ℕ := Nat.choose (2 * G) G
  let Z := cwQ6ExactZWords (n + 1) L G
  letI : Fintype (CWQ6CoupledAddress (n + 1)) :=
    inferInstanceAs (Fintype (Fin 3 → Fin (2 * (n + 1)) → Fin 3))
  letI : Fintype (CWQ6ExactCoupledAddress (n + 1) L G) :=
    Fintype.ofInjective (fun e => e.1) Subtype.val_injective
  let A : (Fin (2 * (n + 1)) → Fin 3) →
      Finset (CWQ6ExactCoupledAddress (n + 1) L G) := fun z =>
    Finset.univ.filter (fun e => e.1 2 = z)
  have hM : 2 < M := by
    dsimp [M]
    have : 1 ≤ Xcount := hX
    nlinarith [sq_nonneg (Xcount : ℤ)]
  have hodd : Odd M := by
    refine ⟨2 * Xcount ^ 2, ?_⟩
    dsimp [M]
    ring
  have h2 : IsUnit (2 : ZMod M) := by
    change IsUnit ((2 : ℕ) : ZMod M)
    rw [ZMod.isUnit_iff_coprime]
    exact hodd.coprime_two_left
  have hB : 0 < B := by
    exact Nat.choose_pos (by omega)
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
      · intro ha
        obtain ⟨e, heA, rfl⟩ := Finset.mem_image.mp ha
        have hez := (Finset.mem_filter.mp heA).2
        have heExact : e.1 ∈ cwQ6ExactAddresses (n + 1) L G := by
          simp only [cwQ6ExactAddresses, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact e.2
        exact Finset.mem_filter.mpr ⟨heExact, hez⟩
      · intro ha
        have ha' := Finset.mem_filter.mp ha
        have hexact := ha'.1
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
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'.2⟩
    calc
      (A z).card = ((A z).image (fun e => e.1)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = Fraw.card := congrArg Finset.card himage
      _ = B := by
        simpa only [Fraw, B] using hregular.z_degree z hz
  have hSrangeM : S ⊆ Finset.range M := by
    intro s hs
    have hslt : s < M / 2 := Finset.mem_range.mp (hSrange hs)
    exact Finset.mem_range.mpr (lt_of_lt_of_le hslt (Nat.div_le_self M 2))
  have hagg := mme_CW_q6_many_retained_z_stars_from_fixed_fiber_moments
    hM h2 hG Z A hzA hAcard hB (by simpa [M, B] using hH) S hSrangeM
  let degree :
      (Fin (2 * (n + 1)) → Fin 3) →
        (Fin (2 * n + 2) → ZMod M) → ℕ := fun z w =>
    ((A z).attach.filter (fun e =>
      ∑ i,
        ((2 * ((e.1.1 0 i).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * w i = 0)).card
  change ∃ w : Fin (2 * n + 2) → ZMod M, ∃ b0 : ZMod M,
      B * S.card * Z.card ≤
        4 * M * (2 * M + B) *
          (Z.filter (fun z => H ≤ degree z w ∧
            ∃ s ∈ S, cwQ6DoubledZHash b0 w z = 2 * (s : ZMod M))).card at hagg
  obtain ⟨w, b0, hcount⟩ := hagg
  let E := cwQ6PrimaryHashBucket (n + 1) L G Xcount S b0 w
  have hsubset :
      Z.filter (fun z => H ≤ degree z w ∧
          ∃ s ∈ S, cwQ6DoubledZHash b0 w z = 2 * (s : ZMod M)) ⊆
        Z.filter (fun z => H ≤ (E.filter (fun e => e.1 2 = z)).card) := by
    intro z hzgood
    have hzparts := Finset.mem_filter.mp hzgood
    apply Finset.mem_filter.mpr
    refine ⟨hzparts.1, ?_⟩
    have hdeg := hzparts.2.1
    have hlabel := hzparts.2.2
    let F := (A z).attach.filter (fun e =>
      ∑ i,
        ((2 * ((e.1.1 0 i).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * w i = 0)
    let I := F.image (fun e => e.1)
    have hcardFI : F.card = I.card := by
      exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
    have hIE : I ⊆ E.filter (fun e => e.1 2 = z) := by
      intro e heI
      obtain ⟨e', heF, rfl⟩ := Finset.mem_image.mp heI
      have heDiff := (Finset.mem_filter.mp heF).2
      have heA := e'.2
      have hez : e'.1.1 2 = z := hzA z hzparts.1 e'.1 heA
      apply Finset.mem_filter.mpr
      refine ⟨?_, hez⟩
      apply (mme_CW_q6_primary_hash_bucket_fixed_z_membership
        (n + 1) L G Xcount S b0 w e'.1).2
      refine ⟨?_, ?_⟩
      · simpa only [M] using heDiff
      · simpa only [hez, M] using hlabel
    have hdegreeCard : degree z w = F.card := by rfl
    rw [hdegreeCard, hcardFI] at hdeg
    exact hdeg.trans (Finset.card_le_card hIE)
  have hcardSubset := Finset.card_le_card hsubset
  refine ⟨w, b0, ?_⟩
  have hZcard := hregular.z_word_card
  change B * S.card *
      (Nat.choose (2 * (n + 1)) L * Nat.choose (2 * (n + 1) - L) L) ≤
    4 * M * (2 * M + B) *
      (Z.filter (fun z => H ≤ (E.filter (fun e => e.1 2 = z)).card)).card
  rw [← hZcard]
  exact hcount.trans (Nat.mul_le_mul_left (4 * M * (2 * M + B)) hcardSubset)
