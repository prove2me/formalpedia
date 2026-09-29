-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellP_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:49:05.140509+00:00
-- url     : https://prove2.me/submissions/995f50b4-e931-4f8e-ab9a-69061b41b4ee

-- Sol generated from Novelty/PellSpineCore.lean
import Mathlib
import Definitions.Def_Novelty_PellSpineCore
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_add_two
/-
# The Pell spine: core arithmetic of the silver-ratio recursion

The *silver ratio* `1 + √2` is the fundamental unit of `ℤ[√2]`, and it already appears
throughout the catalog (`Novelty.BerggrenTreeCriticalLine.silverUnit`,
`Novelty.HyperbolicBerggrenSilverGrowth.silver`, `Shared.BerggrenTQC.SilverSpectrum`).
Its integral shadow is the pair of sequences

* `pellP` : `0, 1, 2, 5, 12, 29, 70, 169, 408, …`  (Pell numbers, OEIS A000129)
* `pellQ` : `1, 1, 3, 7, 17, 41, 99, 239, 577, …`  (half-companion Pell, OEIS A001333)

determined by `(1 + √2)ⁿ = pellQ n + pellP n · √2`.

This file develops the *core* arithmetic of the pair — everything the downstream files
(`Novelty.PellSpineDivisibility`, `Novelty.PellSpinePythagorean`) need:

* `pellP_add`, `pellQ_add` — the two addition laws, proved by a single simultaneous
  two-step induction;
* `pell_equation` — `Q n ^ 2 - 2 * P n ^ 2 = (-1)^n` over `ℤ`, the unit-norm identity;
* `pellP_coprime_pellQ` — its immediate corollary, the key coprimality input for the
  strong-divisibility theory;
* `pellMat_pow` — the *algebraic bridge*: `!![2,1;1,0] ^ (n+1) = !![P (n+2), P (n+1); P (n+1), P n]`,
  from which `pell_cassini` drops out of multiplicativity of the determinant;
* growth and monotonicity facts.

No result here is definitional: each identity needs either an induction or the
determinant bridge.
-/

open Catalog.Novelty.PellSpine

/-! ## Definitions -/




theorem pellQ_add_two (n : ℕ) : pellQ (n + 2) = 2 * pellQ (n + 1) + pellQ n := rfl

/-! ## The mutual one-step laws -/

/-- The two one-step laws, proved simultaneously: each feeds the other. -/
theorem pell_succ_aux (n : ℕ) :
    pellP (n + 1) = pellP n + pellQ n ∧ pellQ (n + 1) = pellQ n + 2 * pellP n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      obtain ⟨hP, hQ⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [pellP_add_two, hP, hQ]; ring
      · rw [pellQ_add_two, hP, hQ]; ring






/-! ## Addition laws

The two laws must be proved *together*: each inductive step feeds the other. -/







/-! ## The Pell equation and coprimality -/



/-! ## Growth -/







/-! ## The algebraic bridge: powers of the silver matrix -/





open Catalog.Novelty.PellSpine in
theorem solution(n : ℕ) : pellP (n + 1) = pellP n + pellQ n := (pell_succ_aux n).1
