-- Prove2me | solution 1 for Round7Agreement.agree_card_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:46:46.599028+00:00
-- url     : https://prove2.me/submissions/99a92e42-cb85-463c-acca-97025218143e

import Mathlib
import Definitions.Def_Tropical_Round7AgreementCharacter
open Round7Agreement Finset in
theorem solution {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Fact p.Prime] [Fact q.Prime]
    [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2) (hpq : p ≠ q) :
    2 * (agree p q).card = Nat.totient (p * q) := by
  -- a unit that is a non-residue mod `p` and a residue mod `q`
  have hflip : ∃ u : (ZMod (p * q))ˣ, chiP p q u = -1 ∧ chiQ p q u = 1 := by
    have hpp : p.Prime := Fact.out
    have hqq : q.Prime := Fact.out
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqq).mpr hpq
    -- a quadratic non-residue `a` mod the odd prime `p`
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p)
      (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, quadraticChar_zero] at ha
      norm_num at ha
    -- CRT: lift `(a, 1)` to `ℤ/pqℤ`
    let e := ZMod.chineseRemainder hcop
    have hfst : ∀ y : ZMod (p * q), (e y).1 = redP p q y := by
      intro y
      show (ZMod.cast y : ZMod p × ZMod q).1 = _
      rw [Prod.fst_zmod_cast, redP, ZMod.castHom_apply]
    have hsnd : ∀ y : ZMod (p * q), (e y).2 = redQ p q y := by
      intro y
      show (ZMod.cast y : ZMod p × ZMod q).2 = _
      rw [Prod.snd_zmod_cast, redQ, ZMod.castHom_apply]
    set x : ZMod (p * q) := e.symm (a, 1) with hxdef
    have hex : e x = (a, 1) := e.apply_symm_apply _
    have hx : IsUnit x :=
      ((Prod.isUnit_iff).mpr ⟨isUnit_iff_ne_zero.mpr ha0, isUnit_one⟩).map e.symm
    have hP : redP p q x = a := by rw [← hfst, hex]
    have hQ : redQ p q x = 1 := by rw [← hsnd, hex]
    refine ⟨hx.unit, ?_, ?_⟩
    · simp only [chiP, IsUnit.unit_spec]
      rw [hP, ha]
    · simp only [chiQ, IsUnit.unit_spec]
      rw [hQ, MulChar.map_one]
  obtain ⟨u₀, h1, h2⟩ := hflip
  have hpp : p.Prime := Fact.out
  have hqq : q.Prime := Fact.out
  -- both characters are multiplicative and `±1` on units
  have hmulP : ∀ u v : (ZMod (p * q))ˣ, chiP p q (u * v) = chiP p q u * chiP p q v := by
    intro u v
    simp only [chiP, Units.val_mul, map_mul]
  have hmulQ : ∀ u v : (ZMod (p * q))ˣ, chiQ p q (u * v) = chiQ p q u * chiQ p q v := by
    intro u v
    simp only [chiQ, Units.val_mul, map_mul]
  have hpmP : ∀ u : (ZMod (p * q))ˣ, chiP p q u = 1 ∨ chiP p q u = -1 := by
    intro u
    exact quadraticChar_dichotomy ((u.isUnit.map (redP p q)).ne_zero)
  have hpmQ : ∀ u : (ZMod (p * q))ˣ, chiQ p q u = 1 ∨ chiQ p q u = -1 := by
    intro u
    exact quadraticChar_dichotomy ((u.isUnit.map (redQ p q)).ne_zero)
  -- multiplying by `u₀` swaps agreement and disagreement
  have hswap : ∀ u : (ZMod (p * q))ˣ,
      (chiP p q (u * u₀) = chiQ p q (u * u₀)) ↔ ¬ (chiP p q u = chiQ p q u) := by
    intro u
    rw [hmulP, hmulQ, h1, h2]
    rcases hpmP u with hu | hu <;> rcases hpmQ u with hv | hv <;> rw [hu, hv] <;> norm_num
  have hcard : (agree p q).card
      = (univ.filter (fun a : (ZMod (p * q))ˣ => ¬ (chiP p q a = chiQ p q a))).card := by
    unfold agree
    apply Finset.card_nbij' (· * u₀⁻¹) (· * u₀)
    · intro u hu
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hu ⊢
      rw [← hswap, inv_mul_cancel_right]
      exact hu
    · intro u hu
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hu ⊢
      rw [hswap]
      exact hu
    · intro u _
      simp
    · intro u _
      simp
  have htot := Finset.card_filter_add_card_filter_not (s := (univ : Finset (ZMod (p * q))ˣ))
    (fun a => chiP p q a = chiQ p q a)
  haveI : NeZero (p * q) := ⟨(Nat.mul_pos hpp.pos hqq.pos).ne'⟩
  rw [card_univ, ZMod.card_units_eq_totient] at htot
  have hA : (agree p q).card = (univ.filter (fun a : (ZMod (p * q))ˣ => chiP p q a = chiQ p q a)).card := rfl
  omega
