-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.containsAP_primes_of_wTricked_offDiagMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:47:18.227805+00:00
-- url     : https://prove2.me/submissions/2c3e9680-1325-4fce-8c7f-9cb36f012306

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_containsAP_of_cyclicAPVal_shortInterval
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_cyclicAP_of_offDiagMass_pos
import Theorems.Thm_Wikipedia_SzemeredisTheorem_wTrickedPrimeWeight_pos_iff

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



namespace Wikipedia.SzemeredisTheorem

























/-- Distributing an affine map across the terms of an arithmetic progression
changes the initial term from `a` to `W * a + r` and the step from `d` to
`W * d`. -/
theorem affine_term (W r a d j : ℕ) :
    W * (a + d * j) + r =
      (W * a + r) + (W * d) * j := by
  simp only [Nat.mul_add, Nat.mul_assoc]
  ac_rfl

/-- Affine lifting for a fixed progression.  If the index progression lies in
the preimage of `A` under `n ↦ W * n + r`, then its affine image is a
progression in `A`.  Positivity of `W` ensures that the new step is positive. -/
theorem IsAPIn.affine {A : Set ℕ} {k a d W r : ℕ}
    (h : IsAPIn {n : ℕ | W * n + r ∈ A} k a d)
    (hW : 0 < W) :
    IsAPIn A k (W * a + r) (W * d) := by
  refine ⟨Nat.mul_pos hW h.1, ?_⟩
  intro j hj
  rw [← affine_term]
  exact h.2 j hj

theorem ContainsAP.affine {A : Set ℕ} {k W r : ℕ}
    (h : ContainsAP {n : ℕ | W * n + r ∈ A} k)
    (hW : 0 < W) :
    ContainsAP A k := by
  obtain ⟨a, d, hap⟩ := h
  exact ⟨W * a + r, W * d, hap.affine hW⟩







end Wikipedia.SzemeredisTheorem

end

section




/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/

namespace Wikipedia.SzemeredisTheorem



@[simp]
theorem mem_greenTaoInterval {N n : ℕ} :
    n ∈ greenTaoInterval N ↔ N / 64 ≤ n ∧ n ≤ N / 4 := by
  simp [greenTaoInterval]

/-- The chosen interval has less than half the width of a full residue
system, which is the hypothesis required by short-interval unwrapping. -/
theorem greenTaoInterval_twice_width_lt {N : ℕ} (hN : 0 < N) :
    2 * (((N / 4 : ℕ) : ℤ) - ((N / 64 : ℕ) : ℤ)) < (N : ℤ) := by
  have hquarter : 2 * (N / 4) < N := by
    omega
  have hquarter_int :
      2 * ((N / 4 : ℕ) : ℤ) < (N : ℤ) := by
    exact_mod_cast hquarter
  have hlower : 0 ≤ ((N / 64 : ℕ) : ℤ) := by
    positivity
  linarith







theorem wTrickedPrimeWeight_nonneg {N : ℕ} [NeZero N]
    {α : ℝ} (hα : 0 ≤ α) (W b : ℕ) (n : ZMod N) :
    0 ≤ wTrickedPrimeWeight α W b n := by
  unfold wTrickedPrimeWeight
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg hα
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h.2.ne_zero)))
  · exact le_rfl













end Wikipedia.SzemeredisTheorem

end
/-!
# Extracting a prime progression from positive W-tricked mass

This module joins the elementary end of the proof.  Once transference gives
positive off-diagonal mass for the W-tricked prime weight, no further
analytic input is needed: positivity identifies prime-supported terms,
short support unwraps the cyclic progression, and the affine W-trick lifts
it to an ordinary progression of natural primes.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
theorem solution
    {k N : ℕ} [NeZero N] (hk : 2 ≤ k)
    {α : ℝ} (hα : 0 < α)
    {W : ℕ} (hW : 0 < W) (b : ℕ)
    (hmass :
      0 <
        cyclicAPOffDiagMass k N
          (wTrickedPrimeWeight α W b)) :
    ContainsAP {p : ℕ | Nat.Prime p} k := by
  have hf :
      ∀ x : ZMod N, 0 ≤ wTrickedPrimeWeight α W b x :=
    wTrickedPrimeWeight_nonneg hα.le W b
  obtain ⟨a, d, hd, hpositive⟩ :=
    exists_cyclicAP_of_offDiagMass_pos hf hmass
  have hpreimage :
      ContainsAP
        {n : ℕ | Nat.Prime (W * n + b)} k := by
    apply containsAP_of_cyclicAPVal_shortInterval
      a d hd hk
      ((N / 64 : ℕ) : ℤ) ((N / 4 : ℕ) : ℤ)
    · intro j hj
      let jf : Fin k := ⟨j, hj⟩
      have hjpos := hpositive jf
      have hsupport :=
        (wTrickedPrimeWeight_pos_iff hα hW b
          (cyclicAPTerm a d jf)).mp hjpos
      have hb := mem_greenTaoInterval.mp hsupport.1
      have hbInt :
          ((N / 64 : ℕ) : ℤ) ≤
              ((cyclicAPTerm a d jf).val : ℤ) ∧
            ((cyclicAPTerm a d jf).val : ℤ) ≤
              ((N / 4 : ℕ) : ℤ) := by
        exact_mod_cast hb
      change
        ((N / 64 : ℕ) : ℤ) ≤ cyclicAPVal a d j ∧
          (cyclicAPVal a d j : ℤ) ≤ ((N / 4 : ℕ) : ℤ)
      simpa only [cyclicAPVal, cyclicAPTerm, jf] using hbInt
    · exact greenTaoInterval_twice_width_lt (NeZero.pos N)
    · intro j hj
      let jf : Fin k := ⟨j, hj⟩
      have hjpos := hpositive jf
      have hprime :=
        ((wTrickedPrimeWeight_pos_iff hα hW b
          (cyclicAPTerm a d jf)).mp hjpos).2
      simpa [wTrickedValue, cyclicAPVal, cyclicAPTerm, jf] using hprime
  exact hpreimage.affine hW
