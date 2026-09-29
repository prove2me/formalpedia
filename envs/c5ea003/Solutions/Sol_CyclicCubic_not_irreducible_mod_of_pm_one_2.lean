-- Prove2me | solution 2 for CyclicCubic.not_irreducible_mod_of_pm_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:41:47.60298+00:00
-- url     : https://prove2.me/submissions/5258de09-6cdc-4abb-8e9e-09b1b554db91

import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting

open Matrix Polynomial CyclicCubic in
theorem solution (p : ℕ) [hp : Fact p.Prime] (hpm : (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6) :
    ¬ Irreducible (fpoly (ZMod p)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  -- `p ≡ ±1 (mod 7)`
  have hmod : p % 7 = 1 ∨ p % 7 = 6 := by
    rcases hpm with h | h
    · left
      have := (ZMod.natCast_eq_natCast_iff' p 1 7).1 (by rw [h, Nat.cast_one])
      simpa using this
    · right
      have := (ZMod.natCast_eq_natCast_iff' p 6 7).1 (by rw [h]; rfl)
      simpa using this
  -- a primitive 7th root of unity in `GF(p²)`
  classical
  let K := GaloisField p 2
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by norm_num)
  have h7 : 7 ∣ Fintype.card Kˣ := by
    rw [Fintype.card_units, hcardK]
    have h1 : p ^ 2 % 7 = 1 := by
      rw [Nat.pow_mod]
      rcases hmod with h | h <;> rw [h]
    have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 7 h7
  let ζ : K := (g : K)
  have hζ7 : ζ ^ 7 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    have := congrArg Units.val h
    simpa [ζ] using this
  have hζ1 : ζ ≠ 1 := by
    intro h
    have hg1 : g = 1 := Units.val_eq_one.1 h
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  have hgeom : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
    have h : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6) = 0 := by
      linear_combination hζ7
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hζ1)
  -- `η = ζ + ζ⁶` is a root of the cubic
  let η : K := ζ + ζ ^ 6
  have hη : η ^ 3 + η ^ 2 - 2 * η - 1 = 0 := by
    linear_combination (ζ ^ 11 + 3 * ζ ^ 6 + ζ ^ 5 + ζ ^ 4 + 3 * ζ + 2) * hζ7 + hgeom
  -- Frobenius fixes `η` because `p ≡ ±1 (mod 7)`
  have hred : ∀ m : ℕ, ζ ^ m = ζ ^ (m % 7) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m 7, pow_add, pow_mul, hζ7, one_pow, one_mul]
  have hηfix : η ^ p = η := by
    have hfrob : η ^ p = ζ ^ p + (ζ ^ p) ^ 6 := by
      rw [show η = ζ + ζ ^ 6 from rfl, add_pow_char ζ (ζ ^ 6), ← pow_mul, ← pow_mul, mul_comm]
    rw [hfrob]
    rcases hmod with h | h
    · rw [hred p, h, pow_one]
    · rw [hred p, h, ← pow_mul, hred (6 * 6)]
      norm_num
      exact add_comm _ _
  -- elements fixed by Frobenius lie in the prime field
  have hmem : ∃ r : ZMod p, algebraMap (ZMod p) K r = η := by
    by_contra hnot
    simp only [not_exists] at hnot
    have hp1 : 1 < p := hp.out.one_lt
    have hP0 := FiniteField.X_pow_card_sub_X_ne_zero K hp1
    have hPdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hp1
    have hS : insert η (Finset.univ.image (algebraMap (ZMod p) K)) ⊆
        (X ^ p - X : K[X]).roots.toFinset := by
      intro s hs
      rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot, eval_sub, eval_pow, eval_X]
      rcases Finset.mem_insert.1 hs with rfl | hs
      · rw [hηfix, sub_self]
      · obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hs
        rw [← map_pow, ZMod.pow_card, sub_self]
    have hηnot : η ∉ Finset.univ.image (algebraMap (ZMod p) K) := by
      intro h
      obtain ⟨r, -, hr⟩ := Finset.mem_image.1 h
      exact hnot r hr
    have hcard : (insert η (Finset.univ.image (algebraMap (ZMod p) K))).card = p + 1 := by
      rw [Finset.card_insert_of_notMem hηnot,
        Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective,
        Finset.card_univ, ZMod.card]
    have hle := ((Finset.card_le_card hS).trans (Multiset.toFinset_card_le _)).trans
      (Polynomial.card_roots' (X ^ p - X : K[X]))
    rw [hcard, hPdeg] at hle
    omega
  obtain ⟨r, hr⟩ := hmem
  have hroot : r ^ 3 + r ^ 2 - 2 * r - 1 = 0 := by
    apply (algebraMap (ZMod p) K).injective
    rw [map_zero, map_sub, map_sub, map_add, map_pow, map_pow, map_mul, map_one, hr]
    rw [show (algebraMap (ZMod p) K) 2 = 2 from map_ofNat _ 2]
    exact hη
  -- an irreducible polynomial with a root has degree one; the cubic has degree three
  intro hirr
  have hIsRoot : (fpoly (ZMod p)).IsRoot r := by
    simp only [fpoly, IsRoot, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_one,
      eval_ofNat]
    exact hroot
  have hdeg1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hIsRoot
  have hdeg3 : (fpoly (ZMod p)).degree = 3 := by
    unfold fpoly
    compute_degree!
  rw [hdeg3] at hdeg1
  exact absurd hdeg1 (by decide)
