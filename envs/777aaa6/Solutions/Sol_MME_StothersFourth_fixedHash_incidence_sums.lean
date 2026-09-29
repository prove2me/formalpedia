-- Prove2me | solution 1 for MME.StothersFourth.fixedHash_incidence_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:47:06.351555+00:00
-- url     : https://prove2.me/submissions/919a9b23-4e7c-4408-afc7-ce00f4001984

import Definitions.Def_mme_stothers_fixed_affine_hash
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card
import Theorems.Thm_mme_ZMod_prime_affine_collision_parameter_card_le
import Theorems.Thm_mme_lower_half_ZMod_image_card
import Theorems.Thm_mme_finset_incidence_double_count

set_option warningAsError true

open MME BigOperators

namespace MME.StothersFourth

set_option autoImplicit false
set_option maxRecDepth 10000

/-- The three doubled `d = 8` hashes form an arithmetic progression on every
coordinatewise-supported mixed edge. -/
private theorem fixedHash_doubled_AP_identity
    {R : Type} [CommSemiring R] {m : ℕ}
    (b0 : R) (w : Fin (fixedOuterLength m) → R)
    (x y z : FixedOuterAddress m)
    (hsupp : FixedCoordinatewiseSupported (fixedMixedAddress x y z)) :
    fixedHashDoubledX w (x 0) + fixedHashDoubledY b0 w (y 1) =
      2 * fixedHashDoubledZ b0 w (z 2) := by
  simp only [fixedHashDoubledX, fixedHashDoubledY, fixedHashDoubledZ]
  have hsum :
      (∑ k, (((2 * (x 0 k).val : ℕ) : R) * w k)) +
          (∑ k, (((2 * (y 1 k).val : ℕ) : R) * w k)) =
        2 * ∑ k, (((8 - (z 2 k).val : ℕ) : R) * w k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hk : (x 0 k).val + (y 1 k).val + (z 2 k).val = 8 := by
      simpa [fixedMixedAddress, Fin.sum_univ_succ, add_assoc] using hsupp k
    have hxy :
        (x 0 k).val + (y 1 k).val = 8 - (z 2 k).val := by
      omega
    have hxyR :
        ((x 0 k).val : R) + ((y 1 k).val : R) =
          ((8 - (z 2 k).val : ℕ) : R) := by
      rw [← Nat.cast_add]
      exact congrArg (fun n : ℕ ↦ (n : R)) hxy
    push_cast
    calc
      2 * ((x 0 k).val : R) * w k +
          2 * ((y 1 k).val : R) * w k =
          2 * (((x 0 k).val : R) + ((y 1 k).val : R)) * w k := by
            ring
      _ = 2 * (((8 - (z 2 k).val : ℕ) : R) * w k) := by
            rw [hxyR]
            ring
  calc
    (∑ k, (((2 * (x 0 k).val : ℕ) : R) * w k)) +
          (2 * b0 + ∑ k, (((2 * (y 1 k).val : ℕ) : R) * w k)) =
        2 * b0 +
          ((∑ k, (((2 * (x 0 k).val : ℕ) : R) * w k)) +
            ∑ k, (((2 * (y 1 k).val : ℕ) : R) * w k)) := by
      ring
    _ = 2 * b0 +
        2 * ∑ k, (((8 - (z 2 k).val : ℕ) : R) * w k) := by
      rw [hsum]
    _ = 2 *
        (b0 + ∑ k, (((8 - (z 2 k).val : ℕ) : R) * w k)) := by
      ring

/-- Odd moduli turn the doubled identity into the ordinary modular
arithmetic-progression identity. -/
private theorem fixedHash_modular_AP_identity
    {M m : ℕ} (hM : Odd M)
    (b0 : ZMod M) (w : Fin (fixedOuterLength m) → ZMod M)
    (x y z : FixedOuterAddress m)
    (hsupp : FixedCoordinatewiseSupported (fixedMixedAddress x y z)) :
    fixedHashXMod w (x 0) + fixedHashYMod b0 w (y 1) =
      2 * fixedHashZMod b0 w (z 2) := by
  have hunit : IsUnit (2 : ZMod M) :=
    (ZMod.isUnit_iff_coprime 2 M).2 hM.coprime_two_left
  have hAP := fixedHash_doubled_AP_identity b0 w x y z hsupp
  simp only [fixedHashXMod, fixedHashYMod, fixedHashZMod]
  calc
    (2 : ZMod M)⁻¹ * fixedHashDoubledX w (x 0) +
          (2 : ZMod M)⁻¹ * fixedHashDoubledY b0 w (y 1) =
        (2 : ZMod M)⁻¹ *
          (fixedHashDoubledX w (x 0) +
            fixedHashDoubledY b0 w (y 1)) := by ring
    _ = (2 : ZMod M)⁻¹ *
        (2 * fixedHashDoubledZ b0 w (z 2)) := by rw [hAP]
    _ = fixedHashDoubledZ b0 w (z 2) := by
      rw [← mul_assoc, ZMod.inv_mul_of_unit (2 : ZMod M) hunit, one_mul]
    _ = 2 * ((2 : ZMod M)⁻¹ *
        fixedHashDoubledZ b0 w (z 2)) := by
      rw [← mul_assoc, ZMod.mul_inv_of_unit (2 : ZMod M) hunit, one_mul]

/-- Linear-affine normal forms for the first two hashes. -/
private theorem fixedHash_XY_normal_forms
    {p N : ℕ} (hpodd : Odd p)
    (b0 : ZMod p) (w : Fin N → ZMod p)
    (x y : Fin N → Fin 9) :
    fixedHashXMod w x = ∑ k, ((x k).val : ZMod p) * w k ∧
      fixedHashYMod b0 w y =
        b0 + ∑ k, ((y k).val : ZMod p) * w k := by
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left
  have htwo : (2 : ZMod p)⁻¹ * 2 = 1 :=
    ZMod.inv_mul_of_unit 2 hunit
  constructor
  · simp only [fixedHashXMod, fixedHashDoubledX]
    rw [show (∑ k, ((2 * (x k).val : ℕ) : ZMod p) * w k) =
        2 * ∑ k, ((x k).val : ZMod p) * w k by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring]
    rw [← mul_assoc, htwo, one_mul]
  · simp only [fixedHashYMod, fixedHashDoubledY]
    rw [show (∑ k, ((2 * (y k).val : ℕ) : ZMod p) * w k) =
        2 * ∑ k, ((y k).val : ZMod p) * w k by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring]
    calc
      (2 : ZMod p)⁻¹ * (2 * b0 + 2 *
          ∑ k, ((y k).val : ZMod p) * w k) =
          ((2 : ZMod p)⁻¹ * 2) *
            (b0 + ∑ k, ((y k).val : ZMod p) * w k) := by ring
      _ = b0 + ∑ k, ((y k).val : ZMod p) * w k := by
        rw [htwo, one_mul]

/-- Two distinct mode words determine an address in the grade-sum-eight
support. -/
private theorem fixedHash_supported_two_modes_determine_address
    {m : ℕ} {a b : FixedOuterAddress m}
    (ha : FixedCoordinatewiseSupported a)
    (hb : FixedCoordinatewiseSupported b)
    {i k : Fin 3} (hik : i ≠ k)
    (hi : a i = b i) (hk : a k = b k) :
    a = b := by
  funext r j
  have hi_j : a i j = b i j := congrFun hi j
  have hk_j : a k j = b k j := congrFun hk j
  by_cases hri : r = i
  · simpa only [hri] using hi_j
  by_cases hrk : r = k
  · simpa only [hrk] using hk_j
  apply Fin.ext
  have hi_val : (a i j).val = (b i j).val := congrArg Fin.val hi_j
  have hk_val : (a k j).val = (b k j).val := congrArg Fin.val hk_j
  have ha_j : (a 0 j).val + (a 1 j).val + (a 2 j).val = 8 := by
    simpa [Fin.sum_univ_succ, add_assoc] using ha j
  have hb_j : (b 0 j).val + (b 1 j).val + (b 2 j).val = 8 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hb j
  fin_cases i <;> fin_cases k <;> fin_cases r <;>
    simp_all <;> omega

/-- Every positive-scale fixed marginal word contains grade one. -/
private theorem fixedHash_marginal_address_has_grade_one
    (m : ℕ) (hm : 0 < m)
    (a : FixedMarginalSupportedAddress m) (i : Fin 3) :
    ∃ k : Fin (fixedOuterLength m), a.1 i k = (1 : Fin 9) := by
  have hcard := a.2.2 i (1 : Fin 9)
  have hpos : 0 < (Finset.univ.filter
      (fun k ↦ a.1 i k = (1 : Fin 9))).card := by
    rw [hcard]
    exact Nat.mul_pos hm (by norm_num [fixedMarginalBaseCount])
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  exact ⟨k, (Finset.mem_filter.mp hk).2⟩

/-- Distinct nine-grade words have a nonzero coordinate difference modulo
every modulus at least nine. -/
private theorem fixedHash_Fin9_word_difference_nonzero
    {p N : ℕ} (hp : 9 ≤ p)
    (x y : Fin (N + 1) → Fin 9) (hxy : x ≠ y) :
    ∃ k : Fin (N + 1),
      ((x k).val : ZMod p) - ((y k).val : ZMod p) ≠ 0 := by
  have hcoord : ∃ k : Fin (N + 1), x k ≠ y k := by
    by_contra h
    push_neg at h
    exact hxy (funext h)
  obtain ⟨k, hk⟩ := hcoord
  refine ⟨k, ?_⟩
  intro hzero
  have hcast : ((x k).val : ZMod p) = ((y k).val : ZMod p) :=
    sub_eq_zero.mp hzero
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hxlt : (x k).val < p := lt_of_lt_of_le (x k).isLt hp
  have hylt : (y k).val < p := lt_of_lt_of_le (y k).isLt hp
  rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hcast
  exact hk (Fin.ext hcast)

/-- The retained full marginal hypergraph is vertex-closed. -/
private theorem fixedHash_retained_vertex_closed
    (m p : ℕ) (S : Finset ℕ) (b0 : ZMod p)
    (w : Fin (fixedOuterLength m) → ZMod p)
    (hpodd : Odd p)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
    FixedMarginalVertexClosed (fixedHashRetainedEdges m p S b0 w) := by
  classical
  intro x hx y hy z hz hsupp
  simp only [fixedHashRetainedEdges, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx hy hz
  obtain ⟨sx, hsx, hxx, _, _⟩ := hx
  obtain ⟨sy, hsy, _, hyy, _⟩ := hy
  obtain ⟨sz, hsz, _, _, hzz⟩ := hz
  have hap := fixedHash_modular_AP_identity hpodd b0 w
    x.1 y.1 z.1 hsupp
  rw [hxx, hyy, hzz] at hap
  obtain ⟨hxs, hsy'⟩ :=
    mme_threeAP_free_half_modulus_no_collision p S hSrange hSfree
      sx sz sy hsx hsz hsy hap
  have hregular : FixedMarginallyRegular
      (fixedMixedAddress x.1 y.1 z.1) := by
    intro i r
    fin_cases i
    · simpa [fixedMixedAddress] using x.2.2 (0 : Fin 3) r
    · simpa [fixedMixedAddress] using y.2.2 (1 : Fin 3) r
    · simpa [fixedMixedAddress] using z.2.2 (2 : Fin 3) r
  let e : FixedMarginalSupportedAddress m :=
    ⟨fixedMixedAddress x.1 y.1 z.1, hsupp, hregular⟩
  refine ⟨e, ?_, rfl⟩
  simp only [fixedHashRetainedEdges, Finset.mem_filter,
    Finset.mem_univ, true_and]
  refine ⟨sz, hsz, ?_, ?_, ?_⟩
  · calc
      fixedHashXMod w (e.1 0) = fixedHashXMod w (x.1 0) := by rfl
      _ = (sx : ZMod p) := hxx
      _ = (sz : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hxs
  · calc
      fixedHashYMod b0 w (e.1 1) = fixedHashYMod b0 w (y.1 1) := by rfl
      _ = (sy : ZMod p) := hyy
      _ = (sz : ZMod p) :=
        congrArg (fun n : ℕ ↦ (n : ZMod p)) hsy'.symm
  · exact hzz

/-- Crude absolute completion-degree bound, used only to satisfy the generic
prime-selection theorem.  The sharp comparison with the target star is a
separate entropy leaf. -/
private theorem fixedHash_marginal_star_card_le_nine_pow
    (m : ℕ) (i : Fin 3) (a : FixedMarginalSupportedAddress m) :
    ((fixedHashMarginalUniverse m).filter
      (fun b ↦ b.1 i = a.1 i)).card ≤ 9 ^ fixedOuterLength m := by
  classical
  let U := fixedHashMarginalUniverse m
  let star := U.filter (fun b ↦ b.1 i = a.1 i)
  have injectAt (k : Fin 3) (hik : i ≠ k) :
      Function.Injective (fun b : {b // b ∈ star} ↦ b.1.1 k) := by
    intro b c hbc
    apply Subtype.ext
    apply Subtype.ext
    apply fixedHash_supported_two_modes_determine_address
      b.1.2.1 c.1.2.1 hik
    · have hb := (Finset.mem_filter.mp b.2).2
      have hc := (Finset.mem_filter.mp c.2).2
      exact hb.trans hc.symm
    · exact hbc
  have hcard (k : Fin 3) (hik : i ≠ k) :
      star.card ≤ Fintype.card (Fin (fixedOuterLength m) → Fin 9) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_le_of_injective _ (injectAt k hik)
  change star.card ≤ _
  fin_cases i
  · simpa using hcard (1 : Fin 3) (by decide)
  · simpa using hcard (2 : Fin 3) (by decide)
  · simpa using hcard (0 : Fin 3) (by decide)

end MME.StothersFourth


open MME BigOperators

namespace MME.StothersFourth

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem fixedHash_state_universe_card
    (m p : ℕ) [Fact p.Prime] :
    (fixedHashStateUniverse m p).card =
      p ^ (fixedOuterLength m + 2) := by
  classical
  simp only [fixedHashStateUniverse, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [show fixedOuterLength m + 2 =
      (fixedOuterLength m + 1) + 1 by omega]
  exact (pow_succ p (fixedOuterLength m + 1)).symm

/-- Every fixed marginal-supported edge survives in exactly `|S| p^N`
augmented states. -/
private theorem fixedHash_address_parameter_card
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hpodd : Odd p) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (p / 2))
    (a : FixedMarginalSupportedAddress m) :
    (fixedHashStatesRetainingAddress m p S a).card =
      S.card * p ^ fixedOuterLength m := by
  classical
  let N := fixedOuterLength m
  let Smod : Finset (ZMod p) := S.image (fun s : ℕ ↦ (s : ZMod p))
  obtain ⟨k0, hk0⟩ :=
    fixedHash_marginal_address_has_grade_one m hm a (0 : Fin 3)
  let c : Fin (N + 1) → ZMod p :=
    Fin.lastCases 0 (fun k : Fin N ↦ ((a.1 0 k).val : ZMod p))
  let offset : (Fin (N + 1) → ZMod p) → ZMod p := fun W ↦
    (∑ i, c i * W i) -
      ∑ k : Fin N, ((a.1 1 k).val : ZMod p) * W k.castSucc
  have hc : c k0.castSucc ≠ 0 := by
    simp [c, hk0]
  have hlinear (W : Fin (N + 1) → ZMod p) :
      (∑ i, c i * W i) =
        ∑ k : Fin N, ((a.1 0 k).val : ZMod p) * W k.castSucc := by
    rw [Fin.sum_univ_castSucc]
    simp [c]
  have hpred (q : (Fin (N + 1) → ZMod p) × ZMod p) :
      a ∈ fixedHashRetainedEdges m p S q.2
          (fun k ↦ q.1 k.castSucc) ↔
        (∑ i, c i * q.1 i) ∈ Smod ∧ q.2 = offset q.1 := by
    let w : Fin N → ZMod p := fun k ↦ q.1 k.castSucc
    have hnorm := fixedHash_XY_normal_forms
      hpodd q.2 w (a.1 0) (a.1 1)
    constructor
    · intro ha
      simp only [fixedHashRetainedEdges, Finset.mem_filter,
        Finset.mem_univ, true_and] at ha
      obtain ⟨s, hsS, hX, hY, _hZ⟩ := ha
      constructor
      · rw [hnorm.1] at hX
        rw [hlinear]
        exact Finset.mem_image.mpr ⟨s, hsS, hX.symm⟩
      · rw [hnorm.2] at hY
        dsimp [offset]
        apply (eq_sub_iff_add_eq).2
        have hxsum : (∑ i, c i * q.1 i) = (s : ZMod p) := by
          rw [hlinear]
          exact hnorm.1.symm.trans hX
        exact hY.trans hxsum.symm
    · rintro ⟨hlinS, hb⟩
      obtain ⟨s, hsS, hcast⟩ := Finset.mem_image.mp hlinS
      have hX : fixedHashXMod w (a.1 0) = (s : ZMod p) := by
        rw [hnorm.1]
        rw [← hlinear]
        exact hcast.symm
      have hY : fixedHashYMod q.2 w (a.1 1) = (s : ZMod p) := by
        rw [hnorm.2, hb]
        dsimp [offset]
        simp only [w]
        rw [← hcast]
        abel
      have hsupp : FixedCoordinatewiseSupported
          (fixedMixedAddress a.1 a.1 a.1) := by
        simpa [fixedMixedAddress] using a.2.1
      have hap := fixedHash_modular_AP_identity hpodd q.2 w
        a.1 a.1 a.1 hsupp
      rw [hX, hY] at hap
      have htwo : (2 : ZMod p) ≠ 0 :=
        ((ZMod.isUnit_iff_coprime 2 p).2
          hpodd.coprime_two_left).ne_zero
      have hZ : fixedHashZMod q.2 w (a.1 2) = (s : ZMod p) := by
        apply Eq.symm
        apply mul_left_cancel₀ htwo
        simpa [two_mul] using hap
      simp only [fixedHashRetainedEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨s, hsS, hX, hY, hZ⟩
  have hfilter :
      fixedHashStatesRetainingAddress m p S a =
        Finset.univ.filter
          (fun q : (Fin (N + 1) → ZMod p) × ZMod p ↦
            (∑ i, c i * q.1 i) ∈ Smod ∧ q.2 = offset q.1) := by
    simp only [fixedHashStatesRetainingAddress]
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpred q
  change (fixedHashStatesRetainingAddress m p S a).card = S.card * p ^ N
  rw [hfilter]
  rw [mme_ZMod_prime_linear_hash_affine_graph_finset_card
    c k0.castSucc hc Smod offset]
  rw [mme_lower_half_ZMod_image_card p S hSrange]

/-- A distinct colliding target--ambient pair survives in at most `p^N`
augmented states. -/
private theorem fixedHash_pair_collision_card_le
    (m p : ℕ) [Fact p.Prime] (hp9 : 9 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (a b : FixedMarginalSupportedAddress m)
    (hab : a ≠ b) (i : Fin 3) (hshare : a.1 i = b.1 i) :
    ((fixedHashStatesRetainingAddress m p S a ∩
      fixedHashStatesRetainingAddress m p S b).card) ≤
        p ^ fixedOuterLength m := by
  classical
  let N := fixedOuterLength m
  let k : Fin 3 := if i = 0 then 1 else 0
  have hik : i ≠ k := by
    fin_cases i <;> simp [k]
  have hkdiff : a.1 k ≠ b.1 k := by
    intro hk
    have habUnderlying : a.1 = b.1 :=
      fixedHash_supported_two_modes_determine_address
        a.2.1 b.2.1 hik hshare hk
    exact hab (Subtype.ext habUnderlying)
  let xAug : Fin (N + 1) → Fin 9 :=
    Fin.lastCases 0 (fun j : Fin N ↦ a.1 k j)
  let yAug : Fin (N + 1) → Fin 9 :=
    Fin.lastCases 0 (fun j : Fin N ↦ b.1 k j)
  have hxyAug : xAug ≠ yAug := by
    intro hxy
    apply hkdiff
    funext j
    have hj := congrFun hxy j.castSucc
    simpa [xAug, yAug] using hj
  obtain ⟨j0, hj0⟩ :=
    fixedHash_Fin9_word_difference_nonzero hp9 xAug yAug hxyAug
  let c : Fin (N + 1) → ZMod p := fun j ↦
    ((xAug j).val : ZMod p) - ((yAug j).val : ZMod p)
  have hc : c j0 ≠ 0 := by
    simpa [c] using hj0
  let offset : (Fin (N + 1) → ZMod p) → ZMod p := fun W ↦
    (∑ j : Fin N, ((a.1 0 j).val : ZMod p) * W j.castSucc) -
      ∑ j : Fin N, ((a.1 1 j).val : ZMod p) * W j.castSucc
  let P : ((Fin (N + 1) → ZMod p) × ZMod p) → Prop := fun q ↦
    q ∈ fixedHashStatesRetainingAddress m p S a ∧
      q ∈ fixedHashStatesRetainingAddress m p S b
  let B := Finset.univ.filter
    (fun q : (Fin (N + 1) → ZMod p) × ZMod p ↦
      (∑ j, c j * q.1 j) = 0 ∧ q.2 = offset q.1 ∧ P q)
  have hsubset :
      fixedHashStatesRetainingAddress m p S a ∩
          fixedHashStatesRetainingAddress m p S b ⊆ B := by
    intro q hq
    have hqa := (Finset.mem_inter.mp hq).1
    have hqb := (Finset.mem_inter.mp hq).2
    have hqa' : a ∈ fixedHashRetainedEdges m p S q.2
        (fun j ↦ q.1 j.castSucc) := by
      simpa only [fixedHashStatesRetainingAddress,
        Finset.mem_filter, Finset.mem_univ, true_and] using hqa
    have hqb' : b ∈ fixedHashRetainedEdges m p S q.2
        (fun j ↦ q.1 j.castSucc) := by
      simpa only [fixedHashStatesRetainingAddress,
        Finset.mem_filter, Finset.mem_univ, true_and] using hqb
    simp only [fixedHashRetainedEdges, Finset.mem_filter,
      Finset.mem_univ, true_and] at hqa' hqb'
    obtain ⟨sa, _hsaS, hXa, hYa, hZa⟩ := hqa'
    obtain ⟨sb, _hsbS, hXb, hYb, hZb⟩ := hqb'
    let w : Fin N → ZMod p := fun j ↦ q.1 j.castSucc
    have hnormA := fixedHash_XY_normal_forms
      hpodd q.2 w (a.1 0) (a.1 1)
    have hnormB := fixedHash_XY_normal_forms
      hpodd q.2 w (b.1 0) (b.1 1)
    have hhash :
        (if i = 0 then
            fixedHashYMod q.2 w (a.1 1) = fixedHashYMod q.2 w (b.1 1)
          else
            fixedHashXMod w (a.1 0) = fixedHashXMod w (b.1 0)) := by
      fin_cases i
      · simp only [Fin.zero_eta, ↓reduceIte]
        have hlabel : (sa : ZMod p) = (sb : ZMod p) := by
          calc
            (sa : ZMod p) = fixedHashXMod w (a.1 0) := hXa.symm
            _ = fixedHashXMod w (b.1 0) := by
              rw [show a.1 0 = b.1 0 by simpa using hshare]
            _ = (sb : ZMod p) := hXb
        exact hYa.trans (hlabel.trans hYb.symm)
      · simp only [Fin.mk_one]
        have hlabel : (sa : ZMod p) = (sb : ZMod p) := by
          calc
            (sa : ZMod p) = fixedHashYMod q.2 w (a.1 1) := hYa.symm
            _ = fixedHashYMod q.2 w (b.1 1) := by
              rw [show a.1 1 = b.1 1 by simpa using hshare]
            _ = (sb : ZMod p) := hYb
        exact hXa.trans (hlabel.trans hXb.symm)
      · simp only [Fin.reduceFinMk]
        have hlabel : (sa : ZMod p) = (sb : ZMod p) := by
          calc
            (sa : ZMod p) = fixedHashZMod q.2 w (a.1 2) := hZa.symm
            _ = fixedHashZMod q.2 w (b.1 2) := by
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
        Fin.lastCases_last, sub_self, zero_mul, add_zero]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, hsums, sub_self]
    have hoff : q.2 = offset q.1 := by
      dsimp [offset]
      apply (eq_sub_iff_add_eq).2
      calc
        q.2 + ∑ j : Fin N,
            ((a.1 1 j).val : ZMod p) * q.1 j.castSucc =
            fixedHashYMod q.2 w (a.1 1) := hnormA.2.symm
        _ = (sa : ZMod p) := hYa
        _ = fixedHashXMod w (a.1 0) := hXa.symm
        _ = ∑ j : Fin N,
            ((a.1 0 j).val : ZMod p) * q.1 j.castSucc := hnormA.1
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨heq, hoff, hqa, hqb⟩
  calc
    (fixedHashStatesRetainingAddress m p S a ∩
        fixedHashStatesRetainingAddress m p S b).card ≤ B.card :=
      Finset.card_le_card hsubset
    _ ≤ p ^ N := by
      exact mme_ZMod_prime_affine_collision_parameter_card_le
        c j0 hc offset P

/- Exact target incidence and bounded directed-collision incidence over all
augmented hash states. -/
end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp9 : 9 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2)) :
    (∑ q ∈ fixedHashStateUniverse m p,
        (fixedExactTargetEdges (fixedHashEdgesAtState m p S q)).card) =
        (fixedHashAllTargetEdges m).card * S.card *
          p ^ fixedOuterLength m ∧
      (∑ q ∈ fixedHashStateUniverse m p,
        (fixedTargetAmbientCollisions
          (fixedHashEdgesAtState m p S q)).card) ≤
        (fixedHashAllTargetAmbientCollisions m).card *
          p ^ fixedOuterLength m := by
  classical
  let Ω := fixedHashStateUniverse m p
  let T := fixedHashAllTargetEdges m
  let C := fixedHashAllTargetAmbientCollisions m
  let E := fixedHashEdgesAtState m p S
  have hEsubset (q) : E q ⊆ fixedHashMarginalUniverse m := by
    intro a ha
    simp only [fixedHashMarginalUniverse, Finset.mem_univ]
  have htarget (q) :
      fixedExactTargetEdges (E q) = T.filter (fun a ↦ a ∈ E q) := by
    ext a
    simp only [T, fixedHashAllTargetEdges,
      fixedExactTargetEdges, Finset.mem_filter]
    constructor
    · rintro ⟨haE, haTarget⟩
      exact ⟨⟨hEsubset q haE, haTarget⟩, haE⟩
    · rintro ⟨⟨_haU, haTarget⟩, haE⟩
      exact ⟨haE, haTarget⟩
  have hcollision (q) :
      fixedTargetAmbientCollisions (E q) =
        C.filter (fun ab ↦ ab.1 ∈ E q ∧ ab.2 ∈ E q) := by
    ext ab
    simp only [C, fixedHashAllTargetAmbientCollisions,
      fixedTargetAmbientCollisions, fixedExactTargetEdges,
      Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨haE, haTarget⟩, hbE⟩, hne, hi⟩
      exact ⟨⟨⟨⟨hEsubset q haE, haTarget⟩, hEsubset q hbE⟩,
        hne, hi⟩, haE, hbE⟩
    · rintro ⟨⟨⟨⟨_haU, haTarget⟩, _hbU⟩, hne, hi⟩, haE, hbE⟩
      exact ⟨⟨⟨haE, haTarget⟩, hbE⟩, hne, hi⟩
  have hstate (a : FixedMarginalSupportedAddress m) :
      Ω.filter (fun q ↦ a ∈ E q) =
        fixedHashStatesRetainingAddress m p S a := by
    ext q
    simp only [Ω, E, fixedHashStateUniverse, fixedHashEdgesAtState,
      fixedHashStatesRetainingAddress, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hpairstate
      (ab : FixedMarginalSupportedAddress m ×
        FixedMarginalSupportedAddress m) :
      Ω.filter (fun q ↦ ab.1 ∈ E q ∧ ab.2 ∈ E q) =
        fixedHashStatesRetainingAddress m p S ab.1 ∩
          fixedHashStatesRetainingAddress m p S ab.2 := by
    ext q
    simp only [Ω, E, fixedHashStateUniverse, fixedHashEdgesAtState,
      fixedHashStatesRetainingAddress, Finset.mem_filter,
      Finset.mem_inter, Finset.mem_univ, true_and]
  constructor
  · change (∑ q ∈ Ω, (fixedExactTargetEdges (E q)).card) =
      T.card * S.card * p ^ fixedOuterLength m
    calc
      (∑ q ∈ Ω, (fixedExactTargetEdges (E q)).card) =
          ∑ q ∈ Ω, (T.filter (fun a ↦ a ∈ E q)).card := by
            apply Finset.sum_congr rfl
            intro q _hq
            rw [htarget]
      _ = ∑ a ∈ T, (Ω.filter (fun q ↦ a ∈ E q)).card :=
        mme_finset_incidence_double_count Ω T (fun q a ↦ a ∈ E q)
      _ = ∑ a ∈ T, S.card * p ^ fixedOuterLength m := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [hstate]
        exact fixedHash_address_parameter_card m p hm hpodd S hSrange a
      _ = T.card * S.card * p ^ fixedOuterLength m := by
        simp [mul_assoc]
  · change (∑ q ∈ Ω,
      (fixedTargetAmbientCollisions (E q)).card) ≤
        C.card * p ^ fixedOuterLength m
    calc
      (∑ q ∈ Ω, (fixedTargetAmbientCollisions (E q)).card) =
          ∑ q ∈ Ω,
            (C.filter (fun ab ↦ ab.1 ∈ E q ∧ ab.2 ∈ E q)).card := by
              apply Finset.sum_congr rfl
              intro q _hq
              rw [hcollision]
      _ = ∑ ab ∈ C,
          (Ω.filter (fun q ↦ ab.1 ∈ E q ∧ ab.2 ∈ E q)).card :=
        mme_finset_incidence_double_count Ω C
          (fun q ab ↦ ab.1 ∈ E q ∧ ab.2 ∈ E q)
      _ ≤ ∑ ab ∈ C, p ^ fixedOuterLength m := by
        apply Finset.sum_le_sum
        intro ab habC
        rw [hpairstate]
        have habData : ab.1 ≠ ab.2 ∧
            ∃ i : Fin 3, ab.1.1 i = ab.2.1 i := by
          have hfull := habC
          simp only [C, fixedHashAllTargetAmbientCollisions,
            fixedTargetAmbientCollisions, Finset.mem_filter,
            Finset.mem_product] at hfull
          exact hfull.2
        obtain ⟨hne, i, hi⟩ := habData
        exact fixedHash_pair_collision_card_le
          m p hp9 hpodd S ab.1 ab.2 hne i hi
      _ = C.card * p ^ fixedOuterLength m := by simp

