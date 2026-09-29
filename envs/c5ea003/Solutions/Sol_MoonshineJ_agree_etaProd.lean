-- Prove2me | solution 1 for MoonshineJ.agree_etaProd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:24:01.917105+00:00
-- url     : https://prove2.me/submissions/3b791079-c12e-4a18-993e-fc5d645a2793

-- Sol generated from Shared/MoonshineJExpansion.lean
import Mathlib
import Definitions.Def_Shared_MoonshineJExpansion
import Theorems.Thm_MoonshineJ_AgreeBelow_mul
import Theorems.Thm_MoonshineJ_AgreeBelow_refl
import Theorems.Thm_MoonshineJ_AgreeBelow_trans
import Theorems.Thm_MoonshineJ_agree_mulT
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







lemma AgreeBelow.pow {N : ℕ} {f g : PowerSeries ℤ} (h : AgreeBelow N f g) :
    ∀ m : ℕ, AgreeBelow N (f ^ m) (g ^ m) := by
  intro m
  induction m with
  | zero => simpa using AgreeBelow.refl N 1
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact MoonshineJ.AgreeBelow.mul ih h


/-! ## 3. The list arithmetic computes power-series arithmetic -/



lemma agree_oneT (N : ℕ) : AgreeBelow N (ser (oneT N)) 1 := by
  intro n hn
  rw [coeff_ser, oneT, cf_map_range _ hn, PowerSeries.coeff_one]

lemma agree_powT (N : ℕ) (a : List ℤ) : ∀ m : ℕ,
    AgreeBelow N (ser (powT N a m)) ((ser a) ^ m)
  | 0 => by simpa [powT] using agree_oneT N
  | m + 1 => by
      refine MoonshineJ.AgreeBelow.trans (agree_mulT N a (powT N a m)) ?_
      rw [pow_succ, mul_comm ((ser a) ^ m) (ser a)]
      exact MoonshineJ.AgreeBelow.mul (AgreeBelow.refl N (ser a)) (agree_powT N a m)

lemma agree_etaAtom (N n : ℕ) (hn : 0 < n) :
    AgreeBelow N (ser (etaAtom N n)) (1 - X ^ n) := by
  intro k hk
  rw [coeff_ser, etaAtom, cf_map_range _ hk, map_sub, PowerSeries.coeff_one,
    PowerSeries.coeff_X_pow]
  rcases eq_or_ne k 0 with rfl | hk0
  · have h0n : (0 : ℕ) ≠ n := hn.ne
    simp [h0n]
  · by_cases hkn : k = n
    · subst hkn; simp [hk0]
    · simp [hk0, hkn]

/-! ## 4. The eta product and the Eisenstein series -/


lemma deltaPart_succ (m : ℕ) :
    deltaPart (m + 1) = deltaPart m * (1 - X ^ (m + 1)) ^ 24 := by
  rw [deltaPart, deltaPart, Finset.prod_Icc_succ_top (by omega)]





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
lemma solution(N : ℕ) : ∀ m : ℕ, AgreeBelow N (ser (etaProd N m)) (deltaPart m) := by
  intro m
  induction m with
  | zero => simpa [etaProd, deltaPart] using agree_oneT N
  | succ n ih =>
      refine MoonshineJ.AgreeBelow.trans (agree_mulT N _ _) ?_
      rw [deltaPart_succ, mul_comm (deltaPart n)]
      exact MoonshineJ.AgreeBelow.mul (MoonshineJ.AgreeBelow.trans (agree_powT N (etaAtom N (n + 1)) 24) (AgreeBelow.pow (agree_etaAtom N (n + 1) (by omega)) 24)) ih
