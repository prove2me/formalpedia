-- Prove2me | solution 1 for mme_CW_2376_augmented_pair_collision_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:16:21.278454+00:00
-- url     : https://prove2.me/submissions/43d68430-0ee6-4194-86bb-c8cb7e5b954f

import Definitions.Def_mme_CW_2376_augmented_hash_states
import Theorems.Thm_mme_ZMod_prime_affine_collision_parameter_card_le
import Theorems.Thm_mme_Fin5_word_difference_nonzero_in_ZMod
import Theorems.Thm_mme_CW_2376_supported_two_modes_determine_address
import Theorems.Thm_mme_CW_2376_modular_hash_XY_normal_forms

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

/-- Two distinct marginal-supported edges that share one mode word are
simultaneously retained in at most `p^N` augmented affine hash states. -/
theorem solution
    (m p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (a b : CW2376MarginalSupportedAddress m)
    (hab : a ≠ b) (i : Fin 3) (hshare : a.1 i = b.1 i) :
    ((cw2376AugmentedHashStatesRetainingAddress m p S a ∩
      cw2376AugmentedHashStatesRetainingAddress m p S b).card) ≤
        p ^ cw2376ProfileLength m := by
  classical
  let N := cw2376ProfileLength m
  let k : Fin 3 := if i = 0 then 1 else 0
  have hik : i ≠ k := by
    fin_cases i <;> simp [k]
  have hkdiff : a.1 k ≠ b.1 k := by
    intro hk
    have habUnderlying : a.1 = b.1 :=
      mme_CW_2376_supported_two_modes_determine_address
        a.2.1 b.2.1 hik hshare hk
    exact hab (Subtype.ext habUnderlying)
  let xAug : Fin (N + 1) → Fin 5 :=
    Fin.lastCases 0 (fun j : Fin N => a.1 k j)
  let yAug : Fin (N + 1) → Fin 5 :=
    Fin.lastCases 0 (fun j : Fin N => b.1 k j)
  have hxyAug : xAug ≠ yAug := by
    intro hxy
    apply hkdiff
    funext j
    have hj := congrFun hxy j.castSucc
    simpa [xAug, yAug] using hj
  obtain ⟨j0, hj0⟩ :=
    mme_Fin5_word_difference_nonzero_in_ZMod hp5 xAug yAug hxyAug
  let c : Fin (N + 1) → ZMod p := fun j =>
    ((xAug j).val : ZMod p) - ((yAug j).val : ZMod p)
  have hc : c j0 ≠ 0 := by
    simpa [c] using hj0
  let offset : (Fin (N + 1) → ZMod p) → ZMod p := fun W =>
    (∑ j : Fin N, ((a.1 0 j).val : ZMod p) * W j.castSucc) -
      ∑ j : Fin N, ((a.1 1 j).val : ZMod p) * W j.castSucc
  let P : ((Fin (N + 1) → ZMod p) × ZMod p) → Prop := fun q =>
    q ∈ cw2376AugmentedHashStatesRetainingAddress m p S a ∧
      q ∈ cw2376AugmentedHashStatesRetainingAddress m p S b
  let B := Finset.univ.filter
    (fun q : (Fin (N + 1) → ZMod p) × ZMod p =>
      (∑ j, c j * q.1 j) = 0 ∧ q.2 = offset q.1 ∧ P q)
  have hsubset :
      cw2376AugmentedHashStatesRetainingAddress m p S a ∩
          cw2376AugmentedHashStatesRetainingAddress m p S b ⊆ B := by
    intro q hq
    have hqa : q ∈ cw2376AugmentedHashStatesRetainingAddress m p S a :=
      (Finset.mem_inter.mp hq).1
    have hqb : q ∈ cw2376AugmentedHashStatesRetainingAddress m p S b :=
      (Finset.mem_inter.mp hq).2
    have hqa' :
        a ∈ cw2376MarginalHashRetainedEdges m p S q.2
          (fun j => q.1 j.castSucc) := by
      simpa only [cw2376AugmentedHashStatesRetainingAddress,
        Finset.mem_filter, Finset.mem_univ, true_and] using hqa
    have hqb' :
        b ∈ cw2376MarginalHashRetainedEdges m p S q.2
          (fun j => q.1 j.castSucc) := by
      simpa only [cw2376AugmentedHashStatesRetainingAddress,
        Finset.mem_filter, Finset.mem_univ, true_and] using hqb
    simp only [cw2376MarginalHashRetainedEdges, Finset.mem_filter,
      Finset.mem_univ, true_and] at hqa' hqb'
    obtain ⟨sa, hsaS, hXa, hYa, hZa⟩ := hqa'
    obtain ⟨sb, hsbS, hXb, hYb, hZb⟩ := hqb'
    let w : Fin N → ZMod p := fun j => q.1 j.castSucc
    have hnormA := mme_CW_2376_modular_hash_XY_normal_forms
      hpodd q.2 w (a.1 0) (a.1 1)
    have hnormB := mme_CW_2376_modular_hash_XY_normal_forms
      hpodd q.2 w (b.1 0) (b.1 1)
    have hhash :
        (if i = 0 then
            cw2376YHashMod q.2 w (a.1 1) =
              cw2376YHashMod q.2 w (b.1 1)
          else
            cw2376XHashMod w (a.1 0) =
              cw2376XHashMod w (b.1 0)) := by
      fin_cases i
      · simp only [Fin.zero_eta, ↓reduceIte]
        have hlabel : (sa : ZMod p) = (sb : ZMod p) := by
          calc
            (sa : ZMod p) = cw2376XHashMod w (a.1 0) := hXa.symm
            _ = cw2376XHashMod w (b.1 0) := by
              rw [show a.1 0 = b.1 0 by simpa using hshare]
            _ = (sb : ZMod p) := hXb
        exact hYa.trans (hlabel.trans hYb.symm)
      · simp only [Fin.mk_one, OfNat.ofNat_ne_zero, ↓reduceIte]
        have hlabel : (sa : ZMod p) = (sb : ZMod p) := by
          calc
            (sa : ZMod p) = cw2376YHashMod q.2 w (a.1 1) := hYa.symm
            _ = cw2376YHashMod q.2 w (b.1 1) := by
              rw [show a.1 1 = b.1 1 by simpa using hshare]
            _ = (sb : ZMod p) := hYb
        exact hXa.trans (hlabel.trans hXb.symm)
      · simp only [Fin.reduceFinMk, OfNat.ofNat_ne_zero, ↓reduceIte]
        have hlabel : (sa : ZMod p) = (sb : ZMod p) := by
          calc
            (sa : ZMod p) = cw2376ZHashMod q.2 w (a.1 2) := hZa.symm
            _ = cw2376ZHashMod q.2 w (b.1 2) := by
              rw [show a.1 2 = b.1 2 by simpa using hshare]
            _ = (sb : ZMod p) := hZb
        exact hXa.trans (hlabel.trans hXb.symm)
    have hsums :
        (∑ j : Fin N, ((a.1 k j).val : ZMod p) * q.1 j.castSucc) =
          ∑ j : Fin N, ((b.1 k j).val : ZMod p) * q.1 j.castSucc := by
      by_cases hi0 : i = 0
      · have hk1 : k = 1 := by simp [k, hi0]
        have hy := hhash
        simp only [hi0, ↓reduceIte] at hy
        rw [hnormA.2, hnormB.2] at hy
        have hy' := add_left_cancel hy
        simpa [hk1, w] using hy'
      · have hk0 : k = 0 := by simp [k, hi0]
        have hx := hhash
        simp only [hi0, ↓reduceIte] at hx
        rw [hnormA.1, hnormB.1] at hx
        simpa [hk0, w] using hx
    have heq : (∑ j, c j * q.1 j) = 0 := by
      rw [Fin.sum_univ_castSucc]
      simp only [c, xAug, yAug, Fin.lastCases_castSucc,
        Fin.lastCases_last, Nat.cast_zero, sub_self, zero_mul, add_zero]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, hsums, sub_self]
    have hoff : q.2 = offset q.1 := by
      dsimp [offset]
      apply (eq_sub_iff_add_eq).2
      calc
        q.2 + ∑ j : Fin N,
            ((a.1 1 j).val : ZMod p) * q.1 j.castSucc =
            cw2376YHashMod q.2 w (a.1 1) := hnormA.2.symm
        _ = (sa : ZMod p) := hYa
        _ = cw2376XHashMod w (a.1 0) := hXa.symm
        _ = ∑ j : Fin N,
            ((a.1 0 j).val : ZMod p) * q.1 j.castSucc := hnormA.1
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨heq, hoff, hqa, hqb⟩
  calc
    (cw2376AugmentedHashStatesRetainingAddress m p S a ∩
        cw2376AugmentedHashStatesRetainingAddress m p S b).card ≤ B.card :=
      Finset.card_le_card hsubset
    _ ≤ p ^ N := by
      exact mme_ZMod_prime_affine_collision_parameter_card_le
        c j0 hc offset P
