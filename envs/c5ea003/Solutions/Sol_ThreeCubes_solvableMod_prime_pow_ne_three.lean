-- Prove2me | solution 1 for ThreeCubes.solvableMod_prime_pow_ne_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:48:58.930721+00:00
-- url     : https://prove2.me/submissions/d6e5fcdd-0a68-4a3f-b353-03a023a88878

-- Sol generated from Probability/LocalSolvability.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_three_cubes_mod_prime_unit

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

/-- Linear congruences with unit leading coefficient are solvable modulo a prime. -/
theorem exists_solve_lin (p : ℕ) (hp : p.Prime) (u s : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    ∃ t : ℤ, (p : ℤ) ∣ u * t + s := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hU : (u : ZMod p) ≠ 0 := fun h => hu ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp h)
  refine ⟨ZMod.cast (-(s : ZMod p) * (u : ZMod p)⁻¹), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  field_simp
  ring

/-- One Hensel step for the equation `x³ = a` at a prime where `3x²` is a unit. -/
theorem cube_lift_step (p : ℕ) (hp : p.Prime) (a x : ℤ) (hx : ¬ (p : ℤ) ∣ 3 * x ^ 2)
    (j : ℕ) (h : (p : ℤ) ^ (j + 1) ∣ x ^ 3 - a) :
    ∃ x' : ℤ, (p : ℤ) ^ (j + 2) ∣ x' ^ 3 - a ∧ (p : ℤ) ∣ x' - x := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, c, hc⟩ := exists_solve_lin p hp (3 * x ^ 2) s hx
  refine ⟨x + t * (p : ℤ) ^ (j + 1), ?_, ⟨t * (p : ℤ) ^ j, by ring⟩⟩
  refine ⟨c + (p : ℤ) ^ j * (3 * x * t ^ 2 + t ^ 3 * (p : ℤ) ^ (j + 1)), ?_⟩
  have h1 : x ^ 3 = a + (p : ℤ) ^ (j + 1) * s := by linarith [hs]
  have h2 : s = (p : ℤ) * c - 3 * x ^ 2 * t := by linarith [hc]
  rw [h2] at h1
  linear_combination h1

/-- **Hensel's lemma for cubes.**  A simple root of `x³ - a` modulo `p` lifts to a root
modulo every power of `p`. -/
theorem cube_lift (p : ℕ) (hp : p.Prime) (a x₀ : ℤ) (hx₀ : ¬ (p : ℤ) ∣ 3 * x₀ ^ 2)
    (h : (p : ℤ) ∣ x₀ ^ 3 - a) (k : ℕ) :
    ∃ x : ℤ, (p : ℤ) ^ (k + 1) ∣ x ^ 3 - a ∧ ¬ (p : ℤ) ∣ 3 * x ^ 2 := by
  induction k with
  | zero => exact ⟨x₀, by simpa using h, hx₀⟩
  | succ j ih =>
      obtain ⟨x, hx1, hx2⟩ := ih
      obtain ⟨x', hx'1, hx'2⟩ := cube_lift_step p hp a x hx2 j hx1
      refine ⟨x', hx'1, fun hcon => hx2 ?_⟩
      obtain ⟨d, hd⟩ := hx'2
      obtain ⟨e, he⟩ := hcon
      exact ⟨e - 3 * d * (x' + x), by linear_combination he - 3 * (x' + x) * hd⟩

/-! ### Step 3: the ramified prime `3` -/



/-! ### Step 4: solvability modulo prime powers -/




/-! ### Step 5: the Chinese remainder theorem -/



/-! ### Main theorem -/





open ThreeCubes in
theorem solution(p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (n : ℤ) (k : ℕ) :
    SolvableMod (p ^ k) n := by
  obtain ⟨x₀, y, z, hdvd, hx₀⟩ := three_cubes_mod_prime_unit p hp n
  set a : ℤ := n - y ^ 3 - z ^ 3 with ha
  have hbase : (p : ℤ) ∣ x₀ ^ 3 - a := by
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c, by rw [ha]; linarith⟩
  have hderiv : ¬ (p : ℤ) ∣ 3 * x₀ ^ 2 := by
    intro hcon
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpp.dvd_mul.mp hcon with h | h
    · have hd3 : p ∣ 3 := by
        have : ((p : ℤ)) ∣ ((3 : ℕ) : ℤ) := by exact_mod_cast h
        exact_mod_cast this
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd3)
    · exact hx₀ (hpp.dvd_of_dvd_pow h)
  obtain ⟨x, hx, -⟩ := cube_lift p hp a x₀ hderiv hbase k
  refine ⟨x, y, z, ?_⟩
  have : (p : ℤ) ^ k ∣ x ^ 3 - a := dvd_trans (pow_dvd_pow _ (by omega)) hx
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by push_cast; rw [ha] at hc; linarith⟩
