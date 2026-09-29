-- Prove2me | solution 1 for D10.necklace_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T09:26:37.089622+00:00
-- url     : https://prove2.me/submissions/97a700ed-db5e-4a4c-93da-f3e0a3cdbd2b

import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10
import Definitions.Def_NumberTheory_MolienNecklaceCongruence
open Classical Finset MulAction in
theorem solution {n : ℕ} [NeZero n] (k : ℕ) :
    n ∣ ∑ a : ZMod n, k ^ Nat.gcd n a.val := by
  have hn0 : n ≠ 0 := NeZero.ne n
  -- orbits of `⟨a⟩` acting on `ℤ/n` by translation: there are `gcd(n, a)` of them
  have horb : ∀ a : ZMod n,
      Nat.card (Quotient (orbitRel (Subgroup.zpowers (Multiplicative.ofAdd a)) (ZMod n)))
        = Nat.gcd n a.val := by
    intro a
    let e : Quotient (orbitRel (Subgroup.zpowers (Multiplicative.ofAdd a)) (ZMod n)) ≃
        ZMod n ⧸ AddSubgroup.zmultiples a :=
      Quotient.congr (Equiv.refl _) (by
        intro x y
        show x ∈ orbit _ y ↔ _
        rw [QuotientAddGroup.leftRel_apply, mem_orbit_iff]
        simp only [Equiv.refl_apply]
        constructor
        · rintro ⟨⟨h, hh⟩, hxy⟩
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
          refine ⟨-m, ?_⟩
          have hxy' : (m • a) + y = x := hxy
          rw [← hxy']
          simp only [neg_smul]
          abel
        · rintro ⟨m, hm⟩
          refine ⟨⟨Multiplicative.ofAdd a ^ (-m), Subgroup.mem_zpowers_iff.mpr ⟨-m, rfl⟩⟩, ?_⟩
          show (-m) • a + y = x
          have hm' : m • a = -x + y := hm
          rw [neg_smul, hm']
          abel)
    rw [Nat.card_congr e]
    have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddSubgroup.zmultiples a)
    rw [Nat.card_zmultiples, Nat.card_zmod] at hcard
    have hord : addOrderOf a = n / Nat.gcd n a.val := by
      rw [← ZMod.natCast_zmod_val a, ZMod.addOrderOf_coe _ hn0, ZMod.natCast_zmod_val]
    rw [hord] at hcard
    have hpos : 0 < n / Nat.gcd n a.val :=
      Nat.div_pos (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hn0)) (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn0))
    have hgcd : Nat.gcd n a.val * (n / Nat.gcd n a.val) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [← hcard, hgcd])
  -- fixed colourings of a rotation are functions on its orbits
  have hfix : ∀ a : ZMod n,
      Fintype.card (fixedBy (D10.Coloring (ZMod n) k) (Multiplicative.ofAdd a)) = k ^ Nat.gcd n a.val := by
    intro a
    rw [← Nat.card_eq_fintype_card, ← horb a, ← Nat.card_fin k, ← Nat.card_fun, Nat.card_fin]
    exact Nat.card_congr (D10.Coloring.fixedEquivOrbitFun (Multiplicative.ofAdd a))
  -- Burnside
  have hB := sum_card_fixedBy_eq_card_orbits_mul_card_group (Multiplicative (ZMod n))
    (D10.Coloring (ZMod n) k)
  have hsum : ∑ g : Multiplicative (ZMod n), Fintype.card (fixedBy (D10.Coloring (ZMod n) k) g)
      = ∑ a : ZMod n, k ^ Nat.gcd n a.val :=
    Fintype.sum_equiv Multiplicative.toAdd _ _ (fun g => hfix (Multiplicative.toAdd g))
  rw [← hsum, hB]
  exact Dvd.intro_left _ (by rw [Fintype.card_multiplicative, ZMod.card])
