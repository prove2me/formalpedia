-- Prove2me | solution 1 for Couret.InterIA.L4.invariant_anti_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:50.584514+00:00
-- url     : https://prove2.me/submissions/29b2b57b-de63-43ea-915f-691d6d9183f6

import Definitions.Def_Couret_L4Foundations_a0fb4bb69682
import Mathlib.Data.Finset.Insert
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false

namespace Couret.InterIA.L4

section Cyclic







end Cyclic

section Rectangle
variable {G : Type*} [AddCommGroup G] [DecidableEq G]



end Rectangle



section Algebra
variable {R : Type*} [CommRing R]









end Algebra

section IntegerCoefficients
variable {α : Type*}

theorem invariant_anti_intersection (τ : α → α) (f : α → ℤ)
    (hinv : ∀ x, f (τ x)=f x) (hanti : ∀ x, f (τ x)= -f x) : f=0 := by
  funext x
  have hi := hinv x
  have ha := hanti x
  change f x=0
  omega

theorem p2m_local_invariant_anti_sum_zero (τ : α → α) (f g : α → ℤ)
    (hinv : ∀ x, f (τ x)=f x) (hanti : ∀ x, g (τ x)= -g x)
    (hsum : ∀ x, f x+g x=0) : f=0 ∧ g=0 := by
  have hg : g=0 := invariant_anti_intersection τ g (by
    intro x
    have h1 := hsum x
    have h2 := hsum (τ x)
    rw [hinv x] at h2
    omega) hanti
  refine ⟨?_,hg⟩
  funext x
  have hx := hsum x
  rw [hg] at hx
  simpa using hx

end IntegerCoefficients

end Couret.InterIA.L4

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (τ : α → α) (f g : α → Int),
  (∀ (x : α), @Eq.{1} Int (f (τ x)) (f x)) →
    (∀ (x : α), @Eq.{1} Int (g (τ x)) (@Neg.neg.{0} Int Int.instNegInt (g x))) →
      (∀ (x : α),
          @Eq.{1} Int (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (f x) (g x))
            (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →
        And
          (@Eq.{p2m_u_0 + 1} (α → Int) f
            (@OfNat.ofNat.{p2m_u_0} (α → Int) (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} (α → Int)
                (@Pi.instZero.{p2m_u_0, 0} α (fun a => Int) fun i =>
                  @MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))))
          (@Eq.{p2m_u_0 + 1} (α → Int) g
            (@OfNat.ofNat.{p2m_u_0} (α → Int) (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} (α → Int)
                (@Pi.instZero.{p2m_u_0, 0} α (fun a => Int) fun i =>
                  @MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))))) := @_root_.Couret.InterIA.L4.p2m_local_invariant_anti_sum_zero

