-- Prove2me | solution 1 for Round7Agreement.exists_flip
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:42:25.761699+00:00
-- url     : https://prove2.me/submissions/ee7ed40d-f0ee-4c4a-94f2-72f16742605f

import Mathlib
import Definitions.Def_Tropical_Round7AgreementCharacter
open Round7Agreement in
theorem solution {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hpq : p ≠ q) :
    ∃ u : (ZMod (p * q))ˣ, chiP p q u = -1 ∧ chiQ p q u = 1 := by
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
