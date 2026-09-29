-- Prove2me | solution 1 for MoonshineJ.j_coefficients_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:57:56.474664+00:00
-- url     : https://prove2.me/submissions/c57a67b3-7596-4cc5-9524-eb7b110cb31f

-- Sol generated from Shared/MoonshineJExpansion.lean
import Mathlib
import Definitions.Def_Shared_MoonshineJExpansion
import Theorems.Thm_MoonshineJ_AgreeBelow_cancel_left
import Theorems.Thm_MoonshineJ_AgreeBelow_mul
import Theorems.Thm_MoonshineJ_AgreeBelow_refl
import Theorems.Thm_MoonshineJ_AgreeBelow_symm
import Theorems.Thm_MoonshineJ_AgreeBelow_trans
import Theorems.Thm_MoonshineJ_agree_e4T
import Theorems.Thm_MoonshineJ_agree_etaProd
import Theorems.Thm_MoonshineJ_agree_mulT
import Theorems.Thm_MoonshineJ_deltaPart_stable
import Theorems.Thm_MoonshineJ_isUnit_deltaPart

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














/-! ## 2. The congruence calculus `≡ mod Xᴺ` -/









/-! ## 3. The list arithmetic computes power-series arithmetic -/






/-! ## 4. The eta product and the Eisenstein series -/







/-! ## 5. Truncation stability: the eta product is well defined -/






/-! ## 6. The verified expansion -/

set_option maxRecDepth 40000 in
/-- The kernel-checked truncated identity `E₄³ = (∏(1-q^k)^24) · J` to eight
terms. -/
theorem list_identity :
    mulT 8 (mulT 8 (e4T 8) (e4T 8)) (e4T 8) = mulT 8 (etaProd 8 7) jT := by decide


/-- **The `q`-expansion of `j`.**  Modulo `q⁸`,
`E₄³ = (∏_{k≥1}(1-q^k)^24) · (1 + 744q + 196884q² + 21493760q³ + ⋯)`.
Since `Δ = q · ∏(1-q^k)^24` and `j = E₄³/Δ`, this says
`j = q⁻¹ + 744 + 196884 q + 21493760 q² + ⋯`. -/
theorem E4_cube_agree_delta_mul_j : AgreeBelow 8 (E4 ^ 3) (deltaPart 7 * jSeries) := by
  have hE : AgreeBelow 8 (ser (mulT 8 (mulT 8 (e4T 8) (e4T 8)) (e4T 8))) (E4 ^ 3) := by
    refine ((agree_mulT 8 _ _).trans (((agree_mulT 8 _ _).trans
      ((agree_e4T 8).mul (agree_e4T 8))).mul (agree_e4T 8))).trans ?_
    rw [pow_succ, pow_two]
  have hD : AgreeBelow 8 (ser (mulT 8 (etaProd 8 7) jT)) (deltaPart 7 * jSeries) :=
    (agree_mulT 8 _ _).trans ((agree_etaProd 8 7).mul (AgreeBelow.refl 8 jSeries))
  rw [list_identity] at hE
  exact hE.symm.trans hD


/-! ## 7. The head-table entry for the identity class -/






/-! ## 8. McKay's observation, on verified numbers

The dimensions of the smallest irreducible representations of the Monster are
`1`, `196883`, `21296876`, `842609326`, `19360062527`, `293553734298`.  The
following identities exhibit the verified `j`-coefficients as non-negative
integral combinations of them — the numerical shadow of the graded Monster
module `V♮`. -/







open MoonshineJ in
theorem solution(f : PowerSeries ℤ) {m : ℕ} (hm : 7 ≤ m)
    (hf : AgreeBelow 8 (E4 ^ 3) (deltaPart m * f)) : AgreeBelow 8 f jSeries := by
  have hstab : AgreeBelow 8 (deltaPart m * jSeries) (deltaPart 7 * jSeries) :=
    (deltaPart_stable (by omega) (by omega)).mul (AgreeBelow.refl 8 jSeries)
  exact AgreeBelow.cancel_left (isUnit_deltaPart m)
    (hf.symm.trans (E4_cube_agree_delta_mul_j.trans hstab.symm))
