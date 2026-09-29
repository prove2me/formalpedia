-- Prove2me | solution 1 for mme_CW_2376_target_address_hash_parameter_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:23:02.223213+00:00
-- url     : https://prove2.me/submissions/dadbf801-9b60-46f0-974c-13fca09e2513

import Definitions.Def_mme_CW_2376_augmented_hash_states
import Theorems.Thm_mme_CW_2376_modular_hash_AP_identity
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card
import Theorems.Thm_mme_CW_2376_modular_hash_XY_normal_forms
import Theorems.Thm_mme_CW_2376_marginal_address_has_grade_one
import Theorems.Thm_mme_lower_half_ZMod_image_card

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

/-- Every marginal-supported CW edge survives in exactly `|S| p^N`
augmented affine hash states.  The extra (unused) weight coordinate makes the
fiber theorem apply with exponent `N`, while the affine offset is uniquely
determined by the equality of the first two hashes. -/
theorem solution
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hpodd : Odd p) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (p / 2))
    (a : CW2376MarginalSupportedAddress m) :
    (cw2376AugmentedHashStatesRetainingAddress m p S a).card =
      S.card * p ^ cw2376ProfileLength m := by
  classical
  let N := cw2376ProfileLength m
  let Smod : Finset (ZMod p) := S.image (fun s : ℕ => (s : ZMod p))
  obtain ⟨j0, hj0⟩ :=
    mme_CW_2376_marginal_address_has_grade_one m hm a (0 : Fin 3)
  let c : Fin (N + 1) → ZMod p :=
    Fin.lastCases 0 (fun j : Fin N => ((a.1 0 j).val : ZMod p))
  let offset : (Fin (N + 1) → ZMod p) → ZMod p := fun W =>
    (∑ i, c i * W i) -
      ∑ j : Fin N, ((a.1 1 j).val : ZMod p) * W j.castSucc
  have hc : c j0.castSucc ≠ 0 := by
    simp [c, hj0]
  have hlinear (W : Fin (N + 1) → ZMod p) :
      (∑ i, c i * W i) =
        ∑ j : Fin N, ((a.1 0 j).val : ZMod p) * W j.castSucc := by
    rw [Fin.sum_univ_castSucc]
    simp [c]
  have hpred (q : (Fin (N + 1) → ZMod p) × ZMod p) :
      a ∈ cw2376MarginalHashRetainedEdges m p S q.2
          (fun j => q.1 j.castSucc) ↔
        (∑ i, c i * q.1 i) ∈ Smod ∧ q.2 = offset q.1 := by
    let w : Fin N → ZMod p := fun j => q.1 j.castSucc
    have hnorm := mme_CW_2376_modular_hash_XY_normal_forms
      hpodd q.2 w (a.1 0) (a.1 1)
    constructor
    · intro ha
      simp only [cw2376MarginalHashRetainedEdges, Finset.mem_filter,
        Finset.mem_univ, true_and] at ha
      obtain ⟨s, hsS, hX, hY, _hZ⟩ := ha
      constructor
      · rw [hnorm.1] at hX
        rw [hlinear]
        exact Finset.mem_image.mpr ⟨s, hsS, hX.symm⟩
      · rw [hnorm.2] at hY
        dsimp [offset]
        apply (eq_sub_iff_add_eq).2
        have hxsum :
            (∑ i, c i * q.1 i) = (s : ZMod p) := by
          rw [hlinear]
          exact hnorm.1.symm.trans hX
        exact hY.trans hxsum.symm
    · rintro ⟨hlinS, hb⟩
      obtain ⟨s, hsS, hcast⟩ := Finset.mem_image.mp hlinS
      have hX : cw2376XHashMod w (a.1 0) = (s : ZMod p) := by
        rw [hnorm.1]
        rw [← hlinear]
        exact hcast.symm
      have hY : cw2376YHashMod q.2 w (a.1 1) = (s : ZMod p) := by
        rw [hnorm.2, hb]
        dsimp [offset]
        simp only [w]
        rw [← hcast]
        abel
      have hsupp : CW2376CoordinatewiseSupported
          (cw2376MixedAddress a.1 a.1 a.1) := by
        simpa [cw2376MixedAddress] using a.2.1
      have hap := mme_CW_2376_modular_hash_AP_identity hpodd q.2 w
        a.1 a.1 a.1 hsupp
      rw [hX, hY] at hap
      have htwo : (2 : ZMod p) ≠ 0 := by
        exact ((ZMod.isUnit_iff_coprime 2 p).2
          hpodd.coprime_two_left).ne_zero
      have hZ : cw2376ZHashMod q.2 w (a.1 2) = (s : ZMod p) := by
        apply Eq.symm
        apply mul_left_cancel₀ htwo
        simpa [two_mul] using hap
      simp only [cw2376MarginalHashRetainedEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨s, hsS, hX, hY, hZ⟩
  have hfilter :
      cw2376AugmentedHashStatesRetainingAddress m p S a =
        Finset.univ.filter
          (fun q : (Fin (N + 1) → ZMod p) × ZMod p =>
            (∑ i, c i * q.1 i) ∈ Smod ∧ q.2 = offset q.1) := by
    simp only [cw2376AugmentedHashStatesRetainingAddress]
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpred q
  change (cw2376AugmentedHashStatesRetainingAddress m p S a).card =
    S.card * p ^ N
  rw [hfilter]
  rw [mme_ZMod_prime_linear_hash_affine_graph_finset_card c j0.castSucc hc
    Smod offset]
  rw [mme_lower_half_ZMod_image_card p S hSrange]
