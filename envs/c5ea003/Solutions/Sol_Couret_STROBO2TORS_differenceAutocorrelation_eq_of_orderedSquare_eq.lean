-- Prove2me | solution 1 for Couret.STROBO2TORS.differenceAutocorrelation_eq_of_orderedSquare_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:51:46.332058+00:00
-- url     : https://prove2.me/submissions/dbb2778c-3f5c-48cf-a517-3a9ebdc37833

import Aesop
import Definitions.Def_Couret_StroboHomometry_90864170804d
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Classical Fourier implication, made explicit for the existing STROBO observable:
equal labelled ordered convolution squares imply equal difference multiplicities.
No converse and no novelty claim. See Lev (2004), section 3, Problem 2, p. 5,
and Riley Casper's observation of 2026-10-15.
-/

open scoped BigOperators ComplexConjugate

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]

omit [AddCommGroup G] in
/-- Evaluation of a finite pair-count distribution against a test function. -/
private theorem pair_count_transform (S : Finset G) (op : G → G → G) (w : G → ℂ) :
    (∑ z : G, ((∑ x ∈ S, ∑ y ∈ S,
      if op x y = z then 1 else 0 : ℕ) : ℂ) * w z) =
      ∑ x ∈ S, ∑ y ∈ S, w (op x y) := by
  simp_rw [Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  simp

theorem orderedSquare_character_transform (S : Finset G) (χ : AddChar G ℂ) :
    (∑ z : G, (orderedSquare S z : ℂ) * χ z) = supportProbe S χ ^ 2 := by
  simp_rw [orderedSquare]
  rw [pair_count_transform]
  simp_rw [AddChar.map_add_eq_mul]
  simp [supportProbe, pow_two, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem differenceAutocorrelation_character_transform (S : Finset G)
    (χ : AddChar G ℂ) :
    (∑ z : G, (differenceAutocorrelation S z : ℂ) * χ z) =
      supportProbe S χ * conj (supportProbe S χ) := by
  simp_rw [differenceAutocorrelation]
  rw [pair_count_transform]
  simp_rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  simp [supportProbe, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Fourier inversion, using mathlib's orthogonality of all complex characters. -/
private theorem character_sum_inversion (f : G → ℂ) (x : G) :
    (∑ χ : AddChar G ℂ, (∑ z : G, f z * χ z) * χ (-x)) =
      f x * (Fintype.card G : ℂ) := by
  simp_rw [Finset.sum_mul, mul_assoc, ← AddChar.map_add_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite]
  simp [add_neg_eq_zero]

/-- The full collection of character sums separates functions. -/
theorem character_sums_injective (f g : G → ℂ)
    (h : ∀ χ : AddChar G ℂ, ∑ z : G, f z * χ z = ∑ z : G, g z * χ z) : f = g := by
  funext x
  have hi := congrArg (fun t : (AddChar G ℂ) → ℂ =>
    ∑ χ : AddChar G ℂ, t χ * χ (-x)) (funext h)
  dsimp at hi
  rw [character_sum_inversion, character_sum_inversion] at hi
  exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hi

/-- Equal complex squares retain only a sign ambiguity at each character. -/
theorem supportProbe_eq_or_neg_of_orderedSquare_eq (S T : Finset G)
    (h : ∀ z : G, orderedSquare S z = orderedSquare T z) (χ : AddChar G ℂ) :
    supportProbe S χ = supportProbe T χ ∨ supportProbe S χ = -supportProbe T χ := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← orderedSquare_character_transform, ← orderedSquare_character_transform]
  simp_rw [h]



/-- General finite-subset theorem: equality of labelled ordered sum counts
implies equality of labelled ordered difference counts, with multiplicities. -/
theorem p2m_local_differenceAutocorrelation_eq_of_orderedSquare_eq (S T : Finset G)
    (h : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    ∀ z : G, differenceAutocorrelation S z = differenceAutocorrelation T z := by
  have hf : (fun z => (differenceAutocorrelation S z : ℂ)) =
      (fun z => (differenceAutocorrelation T z : ℂ)) := by
    apply character_sums_injective
    intro χ
    rw [differenceAutocorrelation_character_transform,
      differenceAutocorrelation_character_transform]
    rcases supportProbe_eq_or_neg_of_orderedSquare_eq S T h χ with hp | hp
    · rw [hp]
    · rw [hp, map_neg, neg_mul_neg]
  intro z
  exact_mod_cast congrFun hf z





end Finite



end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [Fintype.{p2m_u_0} G]
  (S T : Finset.{p2m_u_0} G),
  (∀ (z : G),
      @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
        (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z)) →
    ∀ (z : G),
      @Eq.{1} Nat (@Couret.STROBO2TORS.differenceAutocorrelation.{p2m_u_0} G inst inst_1 S z)
        (@Couret.STROBO2TORS.differenceAutocorrelation.{p2m_u_0} G inst inst_1 T z) := @_root_.Couret.STROBO2TORS.p2m_local_differenceAutocorrelation_eq_of_orderedSquare_eq

