-- Prove2me | solution 1 for ThreeCubes.cubes_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:39:34.003367+00:00
-- url     : https://prove2.me/submissions/3ed7b8c6-9388-48f2-8a85-600c7e25c583

-- Sol generated from Probability/LocalSolvability.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_fiber_card_le_three

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



/-! ### Main theorem -/





open ThreeCubes in
theorem solution(p : ℕ) [hp : Fact p.Prime] :
    p + 2 ≤ 3 * (Finset.image (fun x : ZMod p => x ^ 3) Finset.univ).card := by
  classical
  set C := Finset.image (fun x : ZMod p => x ^ 3) (Finset.univ : Finset (ZMod p)) with hC
  have h0 : (0 : ZMod p) ∈ C := by
    rw [hC, Finset.mem_image]; exact ⟨0, Finset.mem_univ _, by ring⟩
  have key : ∑ c ∈ C, (Finset.univ.filter (fun x : ZMod p => x ^ 3 = c)).card = p := by
    rw [← Finset.card_eq_sum_card_image, Finset.card_univ, ZMod.card p]
  have hz : (Finset.univ.filter (fun x : ZMod p => x ^ 3 = (0 : ZMod p))).card = 1 := by
    have hset : (Finset.univ.filter (fun x : ZMod p => x ^ 3 = (0 : ZMod p))) = {0} := by
      ext x; simp [pow_eq_zero_iff]
    rw [hset]; simp
  have hsplit : ∑ c ∈ C, (Finset.univ.filter (fun x : ZMod p => x ^ 3 = c)).card
      = 1 + ∑ c ∈ C.erase 0, (Finset.univ.filter (fun x : ZMod p => x ^ 3 = c)).card := by
    rw [← Finset.sum_erase_add _ _ h0, hz]; ring
  have hbnd : ∑ c ∈ C.erase 0, (Finset.univ.filter (fun x : ZMod p => x ^ 3 = c)).card
      ≤ 3 * (C.erase 0).card := by
    calc _ ≤ ∑ _c ∈ C.erase 0, 3 := Finset.sum_le_sum (fun c _ => fiber_card_le_three _ c)
      _ = 3 * (C.erase 0).card := by rw [Finset.sum_const]; ring
  have herase : (C.erase 0).card = C.card - 1 := Finset.card_erase_of_mem h0
  have hCpos : 1 ≤ C.card := Finset.card_pos.mpr ⟨0, h0⟩
  omega
