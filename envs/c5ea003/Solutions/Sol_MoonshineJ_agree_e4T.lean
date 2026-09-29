-- Prove2me | solution 1 for MoonshineJ.agree_e4T
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:55:17.156755+00:00
-- url     : https://prove2.me/submissions/3b3c6ca2-0437-4c43-8bfd-733a86b56683

-- Sol generated from Shared/MoonshineJExpansion.lean
import Mathlib
import Definitions.Def_Shared_MoonshineJExpansion
import Theorems.Thm_MoonshineJ_coeff_ser

/-!
# A machine-verified `q`-expansion of the modular invariant `j`

The Monstrous-Moonshine head-character table records, for each of the `194`
conjugacy classes `g` of the Monster, the coefficient `c_g(1)` of `q` in the
McKay–Thompson series `T_g = q⁻¹ + 0 + c_g(1) q + ⋯`.  The entry for the
identity class `1A` is the coefficient of `q` in `j - 744`, i.e. the famous
`196884 = 196883 + 1` of McKay's observation.

This file *computes that entry from first principles inside Lean*, rather than
importing it as unverified data.  The route is purely formal-power-series
arithmetic over `ℤ`:

* `MoonshineJ.E4` is the Eisenstein series `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`, defined by
  its divisor-sum coefficients;
* `MoonshineJ.deltaPart m = ∏_{k=1}^{m} (1 - q^k)^24` is the truncated
  eta-product, so that `Δ = q · deltaPart ∞`;
* `MoonshineJ.deltaPart_stable` proves that the coefficients of `deltaPart m`
  below degree `N` do **not** depend on `m` once `m ≥ N - 1`, which is what makes
  "the" eta product well defined without any convergence theory;
* `MoonshineJ.E4_cube_agree_delta_mul_j` proves
  `E₄³ ≡ deltaPart 7 · J  (mod q⁸)` with
  `J = 1 + 744 q + 196884 q² + 21493760 q³ + 864299970 q⁴ + ⋯`,
  which is exactly the statement `j = q⁻¹ + 744 + 196884 q + ⋯` since
  `j = E₄³/Δ` and `Δ = q · deltaPart`;
* `MoonshineJ.j_coefficients_unique` shows the tabulated coefficients are
  *forced*: any power series `f` with `E₄³ ≡ deltaPart m · f (mod q⁸)` has the
  same first eight coefficients, because `deltaPart m` is a unit of `ℤ⟦X⟧`;
* `MoonshineJ.j_head_coefficient` is the resulting head-table entry
  `c_{1A}(1) = 196884`, and `MoonshineJ.mckay_head_1A` is McKay's
  `196884 = 196883 + 1`.

As a by-product the same computation verifies the first eight values of the
Ramanujan tau function (`MoonshineJ.tau_values`).

## Method

Formal power series are not computable, so the arithmetic is done on *lists of
integers* (truncated series) with an explicit convolution product, and a small
congruence calculus `MoonshineJ.AgreeBelow N` (`≡ mod Xᴺ`) transfers the
list-level identity — discharged by the kernel with `decide` — to genuine
`PowerSeries ℤ` statements.  `MoonshineJ.agreeBelow_iff_dvd` identifies
`AgreeBelow N` with divisibility by `Xᴺ`, which makes the congruence calculus
(products, powers, cancellation by units) pure ideal theory.
-/

open MoonshineJ

open Finset PowerSeries

/-! ## 1. Truncated integer series, represented by lists -/


lemma cf_map_range (f : ℕ → ℤ) {N n : ℕ} (h : n < N) :
    cf ((List.range N).map f) n = f n := by
  have h' : ((List.range N).map f)[n]? = some (f n) := by
    rw [List.getElem?_map, List.getElem?_range h]; rfl
  simp [cf, List.getD_eq_getElem?_getD, h']












/-! ## 2. The congruence calculus `≡ mod Xᴺ` -/









/-! ## 3. The list arithmetic computes power-series arithmetic -/






/-! ## 4. The eta product and the Eisenstein series -/







/-! ## 5. Truncation stability: the eta product is well defined -/






/-! ## 6. The verified expansion -/





/-! ## 7. The head-table entry for the identity class -/






/-! ## 8. McKay's observation, on verified numbers

The dimensions of the smallest irreducible representations of the Monster are
`1`, `196883`, `21296876`, `842609326`, `19360062527`, `293553734298`.  The
following identities exhibit the verified `j`-coefficients as non-negative
integral combinations of them — the numerical shadow of the graded Monster
module `V♮`. -/







open MoonshineJ in
lemma solution(N : ℕ) : AgreeBelow N (ser (e4T N)) E4 := by
  intro n hn
  rw [coeff_ser, e4T, cf_map_range _ hn, E4, coeff_mk]
