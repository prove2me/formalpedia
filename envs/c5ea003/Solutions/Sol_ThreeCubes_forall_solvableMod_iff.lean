-- Prove2me | solution 1 for ThreeCubes.forall_solvableMod_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:56:11.474792+00:00
-- url     : https://prove2.me/submissions/34111a61-4836-481c-ae7c-0f365af653b6

-- Sol generated from Probability/Moduli.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_not_solvableMod_nine
import Theorems.Thm_ThreeCubes_solvableMod_mul
import Theorems.Thm_ThreeCubes_solvableMod_prime_pow_ne_three

/-!
# `9` is the unique obstructing modulus, and five cubes always suffice

Two complements to the local theory.

* `ThreeCubes.forall_solvableMod_iff` : for a positive modulus `m`, *every* integer is a sum
  of three cubes modulo `m` **iff** `9 ∤ m`.  So among all moduli, `9` (and its multiples)
  is the unique source of congruence obstructions for `x³ + y³ + z³`.

* `ThreeCubes.isSumOfFiveCubes` : **every** integer is a sum of five integer cubes.  Together
  with the mod `9` obstruction this pins the "waring number for cubes over `ℤ`" between `4`
  and `5`; the identity `6k = (k+1)³ + (k-1)³ + (-k)³ + (-k)³` also shows every multiple of
  `6` is a sum of four cubes.
-/

open ThreeCubes

/-! ### Solvability modulo `3` -/

/-- Modulo `3` cubing is the identity, so every residue is already a single cube. -/
theorem solvableMod_three (n : ℤ) : SolvableMod 3 n := by
  refine ⟨n, 0, 0, ?_⟩
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  obtain ⟨q, hq⟩ : ∃ q, n = 3 * q + n % 3 := ⟨n / 3, by omega⟩
  rcases h with h | h | h
  · exact ⟨9 * q ^ 3 - q, by rw [hq, h]; ring⟩
  · exact ⟨9 * q ^ 3 + 9 * q ^ 2 + 2 * q, by rw [hq, h]; ring⟩
  · exact ⟨9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2, by rw [hq, h]; ring⟩


/-! ### Five cubes always suffice -/






open ThreeCubes in
theorem solution{m : ℕ} (hm : 0 < m) :
    (∀ n : ℤ, SolvableMod m n) ↔ ¬ (9 ∣ m) := by
  constructor
  · intro h hdvd
    obtain ⟨c, rfl⟩ := hdvd
    obtain ⟨x, y, z, hz⟩ := h 4
    have h9 : SolvableMod 9 (4 : ℤ) := by
      refine ⟨x, y, z, ?_⟩
      have : ((9 : ℤ)) ∣ ((9 * c : ℕ) : ℤ) := by
        push_cast; exact ⟨(c : ℤ), rfl⟩
      exact dvd_trans this hz
    exact not_solvableMod_nine (Or.inl (by norm_num)) h9
  · intro hnd n
    induction m using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp hk =>
        by_cases h3 : p = 3
        · subst h3
          have hk1 : k = 1 := by
            by_contra hc
            exact hnd ⟨3 ^ (k - 2), by
              rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]
              congr 1
              omega⟩
          rw [hk1, pow_one]
          exact solvableMod_three n
        · exact solvableMod_prime_pow_ne_three p hp h3 n k
    | zero => exact absurd hm (by omega)
    | one => exact ⟨0, 0, 0, by simp⟩
    | coprime a b ha hb hab iha ihb =>
        refine solvableMod_mul hab (iha (by omega) ?_) (ihb (by omega) ?_)
        · exact fun hd => hnd (hd.trans (Dvd.intro b rfl))
        · exact fun hd => hnd (hd.trans (Dvd.intro_left a rfl))
