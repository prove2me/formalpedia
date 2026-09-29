-- Prove2me | solution 1 for ThreeCubes.solvableMod_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:45:33.990643+00:00
-- url     : https://prove2.me/submissions/415c060f-dd51-4355-8888-453397b1b313

-- Sol generated from Probability/LocalSolvability.lean
import Mathlib
import Definitions.Def_Probability_Basic

/-!
# The mod 9 congruence is the only local obstruction for sums of three cubes

The main theorem of this file, `ThreeCubes.locallySolvable_iff`, states

  `LocallySolvable n ↔ (n % 9 ≠ 4 ∧ n % 9 ≠ 5)`,

i.e. the congruence `x³ + y³ + z³ ≡ n (mod m)` is solvable for *every* modulus `m > 0`
precisely when the single classical obstruction modulo `9` is absent.  Equivalently the
affine cubic surface `x³ + y³ + z³ = n` has `ℤ_p`-points for every prime `p` exactly when
`n ≢ ±4 (mod 9)`.

The proof combines three ingredients from rather different areas:

* **Additive combinatorics.** The Cauchy–Davenport theorem applied to the set of cubes
  `C ⊆ 𝔽_p` (which satisfies `3|C| ≥ p + 2` because the cubing map is at most `3`-to-`1`
  away from `0` and exactly `1`-to-`1` at `0`) shows `C + C + C = 𝔽_p`; see
  `three_cubes_surjective_mod_prime`.
* **Hensel lifting at unramified primes.** For `p ≠ 3` a solution mod `p` with one
  coordinate a unit lifts to every `p^k`; see `cube_lift`.
* **A ramified analysis at `p = 3`.** The derivative `3x²` has valuation exactly one, so the
  naive Hensel step fails; instead one lifts a unit `u ≡ 1 (mod 9)` to a cube modulo every
  power of `3` (`cube_lift_three`), and then a small case analysis over the seven admissible
  residues mod `9` produces the required representation.

Finally the Chinese remainder theorem glues the prime powers together.
-/

open ThreeCubes

open Finset Pointwise Polynomial

/-! ### Step 1: sums of three cubes cover `𝔽_p` (Cauchy–Davenport) -/






/-! ### Step 2: Hensel lifting away from `3` -/




/-! ### Step 3: the ramified prime `3` -/



/-! ### Step 4: solvability modulo prime powers -/




/-! ### Step 5: the Chinese remainder theorem -/

theorem crt_int {m₁ m₂ : ℤ} (hco : IsCoprime m₁ m₂) (a b : ℤ) :
    ∃ x : ℤ, m₁ ∣ x - a ∧ m₂ ∣ x - b := by
  obtain ⟨u, v, huv⟩ := hco
  refine ⟨b * u * m₁ + a * v * m₂, ⟨u * (b - a), ?_⟩, ⟨v * (a - b), ?_⟩⟩
  · linear_combination a * huv
  · linear_combination b * huv


/-! ### Main theorem -/





open ThreeCubes in
theorem solution{m₁ m₂ : ℕ} (hco : Nat.Coprime m₁ m₂) {n : ℤ}
    (h1 : SolvableMod m₁ n) (h2 : SolvableMod m₂ n) : SolvableMod (m₁ * m₂) n := by
  obtain ⟨x₁, y₁, z₁, hd₁⟩ := h1
  obtain ⟨x₂, y₂, z₂, hd₂⟩ := h2
  have hcoZ : IsCoprime (m₁ : ℤ) (m₂ : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
  obtain ⟨x, hx1, hx2⟩ := crt_int hcoZ x₁ x₂
  obtain ⟨y, hy1, hy2⟩ := crt_int hcoZ y₁ y₂
  obtain ⟨z, hz1, hz2⟩ := crt_int hcoZ z₁ z₂
  have step : ∀ (m : ℕ) (a b c a' b' c' : ℤ), (m : ℤ) ∣ a - a' → (m : ℤ) ∣ b - b' →
      (m : ℤ) ∣ c - c' → (m : ℤ) ∣ a' ^ 3 + b' ^ 3 + c' ^ 3 - n →
      (m : ℤ) ∣ a ^ 3 + b ^ 3 + c ^ 3 - n := by
    intro m a b c a' b' c' ha hb hc hn
    have da : (m : ℤ) ∣ a ^ 3 - a' ^ 3 := ha.trans (sub_dvd_pow_sub_pow a a' 3)
    have db : (m : ℤ) ∣ b ^ 3 - b' ^ 3 := hb.trans (sub_dvd_pow_sub_pow b b' 3)
    have dc : (m : ℤ) ∣ c ^ 3 - c' ^ 3 := hc.trans (sub_dvd_pow_sub_pow c c' 3)
    have := dvd_add (dvd_add (dvd_add da db) dc) hn
    exact (by linarith : a ^ 3 + b ^ 3 + c ^ 3 - n =
      (a ^ 3 - a' ^ 3) + (b ^ 3 - b' ^ 3) + (c ^ 3 - c' ^ 3) +
        (a' ^ 3 + b' ^ 3 + c' ^ 3 - n)) ▸ this
  refine ⟨x, y, z, ?_⟩
  have d1 : (m₁ : ℤ) ∣ x ^ 3 + y ^ 3 + z ^ 3 - n := step m₁ x y z x₁ y₁ z₁ hx1 hy1 hz1 hd₁
  have d2 : (m₂ : ℤ) ∣ x ^ 3 + y ^ 3 + z ^ 3 - n := step m₂ x y z x₂ y₂ z₂ hx2 hy2 hz2 hd₂
  have := hcoZ.mul_dvd d1 d2
  simpa using this
