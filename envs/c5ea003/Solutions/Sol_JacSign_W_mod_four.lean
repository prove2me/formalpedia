-- Prove2me | solution 1 for JacSign.W_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:15:10.484009+00:00
-- url     : https://prove2.me/submissions/e3b7dd07-7e60-418b-be22-9ba6e89a2e71

-- Sol generated from Tropical/JacobiSignedTwoAdic.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore
import Theorems.Thm_JacSign_card_halfSet
import Theorems.Thm_JacSign_chi_neg_one_eq_one
import Theorems.Thm_JacSign_neg_one_notMem_halfSet
import Theorems.Thm_JacSign_sum_eq_two_mul_half

/-!
# The exact 2-adic valuation of the Jacobi-signed circle count

Every observed value of the statistic is `2` times an *odd* number
(`-2, -6, 10, -10, 6, -14, -18, 22, 26, 34, ...`).  This is not a coincidence: we prove

`p ≡ 1 (mod 4) → W p ≡ 2 (mod 4)`  (`JacSign.W_mod_four`),

i.e. `v₂(W p) = 1` exactly.  The argument is a parity count over the "lower half" of the
residues: `W p = 2 S` with `S` a sum of `(p-1)/2` values in `{0, ±1}`, exactly one of which
(the term `x = 1`) vanishes, so `S ≡ (p-1)/2 - 1 ≡ 1 (mod 2)`.

Combined with the Jacobsthal identity of `JacobiSignedTwoSquares.lean` this pins down the
classical normalisation of Fermat's two-square decomposition: `p = a² + b²` with
`a = W p / 2` **odd**.
-/

open Finset

open JacSign

variable (p : ℕ) [Fact p.Prime]


/-- `1` lies in the lower half, `-1` does not. -/
theorem one_mem_halfSet (hp : p ≠ 2) : (1 : ZMod p) ∈ halfSet p := by
  have hprime := (Fact.out : p.Prime)
  have hodd : p % 2 = 1 := hprime.eq_two_or_odd.resolve_left hp
  have hp3 : 3 ≤ p := by have := hprime.two_le; omega
  haveI : NeZero p := ⟨by omega⟩
  have hv : (1 : ZMod p).val = 1 := ZMod.val_one_eq_one_mod p ▸ by
    simp [Nat.mod_eq_of_lt (by omega : 1 < p)]
  refine Finset.mem_erase.mpr ⟨one_ne_zero, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv]
  omega





open JacSign in
theorem solution(hp : p ≠ 2) (h1 : p % 4 = 1) : ∃ s : ℤ, W p = 2 * s ∧ ¬ (2 : ℤ) ∣ s := by
  have hprime := (Fact.out : p.Prime)
  have hp5 : 5 ≤ p := by
    have := hprime.two_le
    rcases (by omega : p = 5 ∨ p < 5 ∨ 5 < p) with h | h | h
    · omega
    · interval_cases p <;> simp_all
    · omega
  set f : ZMod p → ℤ := fun x => quadraticChar (ZMod p) (x * (1 - x ^ 2)) with hf
  have hfneg : ∀ x : ZMod p, f (-x) = f x := by
    intro x
    show quadraticChar (ZMod p) ((-x) * (1 - (-x) ^ 2)) = quadraticChar (ZMod p) (x * (1 - x ^ 2))
    have hx : quadraticChar (ZMod p) ((-x) * (1 - (-x) ^ 2))
        = quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) (x * (1 - x ^ 2)) := by
      rw [← map_mul]; congr 1; ring
    rw [hx, chi_neg_one_eq_one p h1, one_mul]
  have hhalf : W p = 2 * ∑ x ∈ halfSet p, f x := sum_eq_two_mul_half p hp f hfneg (by simp [hf])
  refine ⟨∑ x ∈ halfSet p, f x, hhalf, ?_⟩
  -- the squares of the terms count the nonvanishing ones
  have hsq : ∑ x ∈ halfSet p, (f x) ^ 2 = ((halfSet p).card : ℤ) - 1 := by
    have hone : f 1 = 0 := by simp [hf]
    have hrest : ∀ x ∈ (halfSet p).erase 1, (f x) ^ 2 = 1 := by
      intro x hx
      have hx1 : x ≠ 1 := (Finset.mem_erase.mp hx).1
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
      have hxm1 : x ≠ -1 := by
        intro h
        exact neg_one_notMem_halfSet p hp (h ▸ Finset.mem_of_mem_erase hx)
      have hne : x * (1 - x ^ 2) ≠ 0 := by
        refine mul_ne_zero hx0 ?_
        intro h
        have hx2 : x ^ 2 = 1 := by linear_combination -h
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hx2, one_pow] : x ^ 2 = (1 : ZMod p) ^ 2) with
          h' | h'
        · exact hx1 h'
        · exact hxm1 (by simpa using h')
      exact quadraticChar_sq_one hne
    rw [← Finset.add_sum_erase _ _ (one_mem_halfSet p hp), hone,
      Finset.sum_congr rfl hrest, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (one_mem_halfSet p hp)]
    have hcard : 1 ≤ (halfSet p).card := Finset.card_pos.mpr ⟨1, one_mem_halfSet p hp⟩
    push_cast [Nat.cast_sub hcard]
    ring
  -- each term is congruent to its square mod 2
  have hpar : (2 : ℤ) ∣ (∑ x ∈ halfSet p, (f x) ^ 2) - ∑ x ∈ halfSet p, f x := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun x _ => ?_
    rcases quadraticChar_isQuadratic (ZMod p) (x * (1 - x ^ 2)) with h | h | h <;>
      rw [hf] <;> simp only <;> rw [h] <;> norm_num
  rw [hsq] at hpar
  have hc := card_halfSet p hp
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨m, hm⟩ := hpar
  -- (p-1)/2 is even since p ≡ 1 (mod 4), so the count minus one is odd
  have hp4 : (4 : ℤ) ∣ (p : ℤ) - 1 := by
    obtain ⟨j, hj⟩ : (4 : ℕ) ∣ (p - 1) := by omega
    refine ⟨(j : ℤ), ?_⟩
    have : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [← this, hj]
    push_cast
    ring
  obtain ⟨j, hj⟩ := hp4
  omega
