-- Prove2me | Definitions.Def_Novelty_PellSpineCore
-- name    : Novelty_PellSpineCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:57.59675+00:00
-- url     : https://prove2.me/theorems/6d94ce76-fb24-4778-b408-839296a8b766
-- title:
--   Aether Catalog definitions — Novelty_PellSpineCore
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.PellSpineCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/PellSpineCore.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Novelty.PellSpine

/-! ## Definitions -/

/-- Pell numbers `0, 1, 2, 5, 12, 29, …`: `P (n+2) = 2 * P (n+1) + P n`. -/
def pellP : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pellP (n + 1) + pellP n

/-- Half-companion Pell numbers `1, 1, 3, 7, 17, 41, …`: same recursion, different seed. -/
def pellQ : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * pellQ (n + 1) + pellQ n



/-! ## The mutual one-step laws -/







/-! ## Addition laws

The two laws must be proved *together*: each inductive step feeds the other. -/







/-! ## The Pell equation and coprimality -/



/-! ## Growth -/







/-! ## The algebraic bridge: powers of the silver matrix -/

/-- The silver matrix `!![2,1;1,0]`, the companion matrix of `x² = 2x + 1`. -/
def pellMat : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 0]



end Catalog.Novelty.PellSpine


