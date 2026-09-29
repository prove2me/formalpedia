-- Prove2me | solution 2 for CyclicCubic.root_of_residue_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T17:17:46.651376+00:00
-- url     : https://prove2.me/submissions/20bf437c-b296-4f29-a836-f47f674bbe04

import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting

open Polynomial in
theorem solution (p : ℕ) [hp : Fact p.Prime] (h6 : (p : ZMod 7) = 6) :
    ∃ x : ZMod p, CyclicCubic.fval x = 0 := by
  have hp7 : p ≠ 7 := by
    rintro rfl
    exact absurd h6 (by decide)
  have hpm : (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6 := Or.inr h6
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7p : Nat.Prime 7 := by norm_num
  have hp1 : 1 < p := hp.out.one_lt
  -- the case `p = 2`: the cubic has no root mod 2
  have hQ2' : ∀ x : ZMod 2,
      ¬ (x ^ 3 + x ^ 2 - 2 * x - 1 = 0) := by
    decide
  have hQ2 : p = 2 → ∀ x : ZMod p,
      ¬ (x ^ 3 + x ^ 2 - 2 * x - 1 = 0) := by
    intro h
    subst h
    exact hQ2'
  let K := GaloisField p 2
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by norm_num)
  have hmod : p % 7 = 1 ∨ p % 7 = 6 := by
    rcases hpm with h | h
    · left
      have := (ZMod.natCast_eq_natCast_iff' p 1 7).1 (by rw [h, Nat.cast_one])
      simpa using this
    · right
      have := (ZMod.natCast_eq_natCast_iff' p 6 7).1 (by rw [h]; rfl)
      simpa using this
  have h11 : 7 ∣ Fintype.card Kˣ := by
    rw [Fintype.card_units, hcardK]
    have h1 : p ^ 2 % 7 = 1 := by
      rw [Nat.pow_mod]
      rcases hmod with h | h <;> rw [h]
    have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 7 h11
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : K, ζ = (g : K) := ⟨_, rfl⟩
  have hζ7 : ζ ^ 7 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    have := congrArg Units.val h
    simpa [hζdef] using this
  have hζ1 : ζ ≠ 1 := by
    intro h
    have hg1 : g = 1 := Units.val_eq_one.1 (hζdef ▸ h)
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  have hgeom : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
    have h : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6) = 0 := by
      linear_combination hζ7
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hζ1)
  obtain ⟨η, hηdef⟩ : ∃ η : K, η = ζ + ζ ^ 6 := ⟨_, rfl⟩
  have hη : η ^ 3 + η ^ 2 - 2 * η - 1 = 0 := by
    rw [hηdef]
    linear_combination (ζ ^ 11 + 3 * ζ ^ 6 + ζ ^ 5 + ζ ^ 4 - ζ ^ 3 - ζ ^ 2 + 2 * ζ + 1) * hζ7
      + ζ ^ 4 * hgeom
  have hred : ∀ m : ℕ, ζ ^ m = ζ ^ (m % 7) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m 7, pow_add, pow_mul, hζ7, one_pow, one_mul]
  have hηfix : η ^ p = η := by
    have hfrob : η ^ p = ζ ^ p + (ζ ^ p) ^ 6 := by
      rw [hηdef, add_pow_char ζ (ζ ^ 6), ← pow_mul, ← pow_mul, mul_comm]
    rw [hfrob, hηdef]
    rcases hmod with h | h
    · rw [hred p, h, pow_one]
    · rw [hred p, h, ← pow_mul, hred (6 * 6)]
      norm_num
      exact add_comm _ _
  -- elements fixed by Frobenius lie in the prime field
  have hmem : ∃ r : ZMod p, algebraMap (ZMod p) K r = η := by
    by_contra hnot
    simp only [not_exists] at hnot
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
  refine ⟨r, ?_⟩
  simp only [CyclicCubic.fval]
  apply (algebraMap (ZMod p) K).injective
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, map_ofNat, hr]
  exact hη
