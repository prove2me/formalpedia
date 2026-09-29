-- Prove2me | solution 1 for Round7Agreement.mem_agree_iff_jacobiSym
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:51:45.385313+00:00
-- url     : https://prove2.me/submissions/caaed67b-a919-4dc2-af11-bae8d7fb59c5

import Mathlib
import Definitions.Def_Tropical_Round7AgreementCharacter
open Round7Agreement in
theorem solution {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Fact p.Prime] [Fact q.Prime]
    [Fact p.Prime] [Fact q.Prime] [Fact p.Prime] [Fact q.Prime] (a : (ZMod (p * q))ˣ) :
    a ∈ agree p q ↔ jacobiSym ((a : ZMod (p * q)).val : ℤ) (p * q) = 1 := by
  have hpp : p.Prime := Fact.out
  have hqq : q.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : NeZero q := ⟨hqq.ne_zero⟩
  haveI : NeZero (p * q) := ⟨(Nat.mul_pos hpp.pos hqq.pos).ne'⟩
  -- each character is the Legendre symbol of the representative `a.val`
  have hP : chiP p q a = legendreSym p ((a : ZMod (p * q)).val : ℤ) := by
    unfold chiP legendreSym
    rw [redP, ZMod.castHom_apply, ZMod.cast_eq_val]
    push_cast
    rfl
  have hQ : chiQ p q a = legendreSym q ((a : ZMod (p * q)).val : ℤ) := by
    unfold chiQ legendreSym
    rw [redQ, ZMod.castHom_apply, ZMod.cast_eq_val]
    push_cast
    rfl
  have hpmP : chiP p q a = 1 ∨ chiP p q a = -1 :=
    quadraticChar_dichotomy ((a.isUnit.map (redP p q)).ne_zero)
  have hpmQ : chiQ p q a = 1 ∨ chiQ p q a = -1 :=
    quadraticChar_dichotomy ((a.isUnit.map (redQ p q)).ne_zero)
  -- `J(a | pq) = (a/p)(a/q)`
  rw [jacobiSym.mul_right, ← jacobiSym.legendreSym.to_jacobiSym, ← jacobiSym.legendreSym.to_jacobiSym, ← hP, ← hQ]
  unfold agree
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rcases hpmP with h1 | h1 <;> rcases hpmQ with h2 | h2 <;> rw [h1, h2] <;> norm_num
