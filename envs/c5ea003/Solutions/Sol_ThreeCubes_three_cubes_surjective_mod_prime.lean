-- Prove2me | solution 1 for ThreeCubes.three_cubes_surjective_mod_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:45:34.589518+00:00
-- url     : https://prove2.me/submissions/2dd1e5f3-a77c-43db-b92c-474b928e098f

-- Sol generated from Probability/LocalSolvability.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Theorems.Thm_ThreeCubes_cubes_card

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
theorem solution(p : ℕ) [hp : Fact p.Prime] (a : ZMod p) :
    ∃ x y z : ZMod p, x ^ 3 + y ^ 3 + z ^ 3 = a := by
  classical
  set C := Finset.image (fun x : ZMod p => x ^ 3) (Finset.univ : Finset (ZMod p)) with hC
  have h3 : p + 2 ≤ 3 * C.card := cubes_card p
  have hCne : C.Nonempty := ⟨0, by rw [hC, Finset.mem_image]; exact ⟨0, Finset.mem_univ _, by ring⟩⟩
  have hCp : 1 ≤ C.card := Finset.card_pos.mpr hCne
  have hCCne : (C + C).Nonempty := hCne.add hCne
  have h1 := min_le_iff.mp (ZMod.cauchy_davenport hp.out hCne hCne)
  have h2 := min_le_iff.mp (ZMod.cauchy_davenport hp.out hCCne hCne)
  have huniv : (C + C) + C = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hle := Finset.card_le_univ ((C + C) + C)
    simp only [ZMod.card p] at hle ⊢
    omega
  have hmem : a ∈ (C + C) + C := huniv ▸ Finset.mem_univ a
  rw [Finset.mem_add] at hmem
  obtain ⟨w, hw, z, hz, hwz⟩ := hmem
  rw [Finset.mem_add] at hw
  obtain ⟨u, hu, v, hv, huv⟩ := hw
  rw [hC, Finset.mem_image] at hu hv hz
  obtain ⟨x, _, rfl⟩ := hu
  obtain ⟨y, _, rfl⟩ := hv
  obtain ⟨t, _, rfl⟩ := hz
  exact ⟨x, y, t, by rw [huv]; exact hwz⟩
