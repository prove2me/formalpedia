-- Prove2me | solution 1 for JacSign.sum_eq_two_mul_half
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:10:25.851996+00:00
-- url     : https://prove2.me/submissions/2cf38953-9f32-4fe2-8380-772bd1ff82a1

-- Sol generated from Tropical/JacobiSignedWeilFloorCore.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore

/-!
# The Jacobi-signed circle count: core structure (JACSIGN)

For an odd prime `p` let `χ = quadraticChar (ZMod p)` be the Legendre character and let

`S(p) = {(x, y) ∈ (ZMod p)² : x² + y² = 1}`

be the unit circle over `ZMod p`.  The *Jacobi-signed circle count* is the character
weighted point count

`circleWeight p = ∑_{(x,y) ∈ S(p)} χ(x)`.

This file proves the basic structure of this weight:

* `JacSign.circleWeight_eq_W` : the geometric weight collapses to the **cubic character sum**
  `W p = ∑_x χ(x(1 - x²))`, i.e. the trace of Frobenius of the curve `y² = x - x³`
  (up to sign).
* `JacSign.W_neg_reflect` : the reflection identity `W p = χ(-1) · W p`.
* `JacSign.W_eq_zero_of_three_mod_four` : `W p = 0` whenever `p ≡ 3 (mod 4)` — the
  supersingular half of the primes carries **no** signal at all.
* `JacSign.W_even` : `W p` is always even, so the weight can never be an odd number;
  this matches the observed data `-2, -10, 6, -18, 14, 22`.

These are the structural facts underlying the JACSIGN experiment; the Weil bound
`W p ^ 2 ≤ 4 p` is proved in `JacobiSignedWeilFloorBound.lean`.
-/

open Finset

open JacSign



variable (p : ℕ) [Fact p.Prime]











open JacSign in
theorem solution(hp : p ≠ 2) (f : ZMod p → ℤ)
    (hfneg : ∀ x : ZMod p, f (-x) = f x) (hf0 : f 0 = 0) :
    (∑ x : ZMod p, f x) = 2 * ∑ x ∈ halfSet p, f x := by
  have hprime := (Fact.out : p.Prime)
  have hodd : p % 2 = 1 := hprime.eq_two_or_odd.resolve_left hp
  have hp3 : 3 ≤ p := by
    rcases hprime.two_le.lt_or_eq with h | h
    · omega
    · omega
  haveI : NeZero p := ⟨by omega⟩
  set A : Finset (ZMod p) := univ.filter (fun x => 2 * x.val < p) with hA
  have hsplit : (∑ x : ZMod p, f x)
      = ∑ x ∈ A, f x + ∑ x ∈ univ.filter (fun x : ZMod p => ¬ (2 * x.val < p)), f x :=
    (Finset.sum_filter_add_sum_filter_not univ _ f).symm
  have hval0 : ∀ x : ZMod p, x.val = 0 ↔ x = 0 := fun x => ZMod.val_eq_zero x
  have hne : ∀ x : ZMod p, x ≠ 0 → 2 * x.val ≠ p := by
    intro x _ h
    omega
  have hB : ∑ x ∈ univ.filter (fun x : ZMod p => ¬ (2 * x.val < p)), f x
      = ∑ x ∈ A.erase 0, f x := by
    refine Finset.sum_nbij' (i := fun x => -x) (j := fun x => -x) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha
      have ha0 : a ≠ 0 := by
        intro h; rw [h] at ha; simp at ha; omega
      haveI : NeZero a := ⟨ha0⟩
      have hv : (-a).val = p - a.val := ZMod.val_neg_of_ne_zero a
      have hlt : a.val < p := ZMod.val_lt a
      have hne' : 2 * a.val ≠ p := hne a ha0
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · simpa [neg_eq_zero] using ha0
      · simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, hv]
        omega
    · intro a ha
      have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
      have ha' := (Finset.mem_erase.mp ha).2
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
      haveI : NeZero a := ⟨ha0⟩
      have hv : (-a).val = p - a.val := ZMod.val_neg_of_ne_zero a
      have hlt : a.val < p := ZMod.val_lt a
      have hpos : 0 < a.val := by
        rcases Nat.eq_zero_or_pos a.val with h | h
        · exact absurd ((hval0 a).mp h) ha0
        · exact h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, hv]
      omega
    · intro a _; simp
    · intro a _; simp
    · intro a _; exact (hfneg a).symm
  have hA0 : ∑ x ∈ A, f x = ∑ x ∈ A.erase 0, f x := by
    by_cases h0 : (0 : ZMod p) ∈ A
    · rw [← Finset.add_sum_erase A f h0, hf0, zero_add]
    · rw [Finset.erase_eq_of_notMem h0]
  rw [hsplit, hB, hA0, halfSet, ← hA]
  ring
