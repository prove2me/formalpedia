-- Prove2me | solution 1 for MoonshineJ.deltaPart_stable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:55:15.900331+00:00
-- url     : https://prove2.me/submissions/aa9e9a0d-e293-4329-961f-466153186316

-- Sol generated from Shared/MoonshineJExpansion.lean
import Mathlib
import Definitions.Def_Shared_MoonshineJExpansion
import Theorems.Thm_MoonshineJ_AgreeBelow_mul
import Theorems.Thm_MoonshineJ_AgreeBelow_refl
import Theorems.Thm_MoonshineJ_AgreeBelow_symm
import Theorems.Thm_MoonshineJ_AgreeBelow_trans

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


lemma agreeBelow_iff_dvd {N : ℕ} {f g : PowerSeries ℤ} :
    AgreeBelow N f g ↔ (X : PowerSeries ℤ) ^ N ∣ (f - g) := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h n hn; simpa [sub_eq_zero] using h n hn
  · intro h n hn; have := h n hn; simpa [sub_eq_zero] using this







/-! ## 3. The list arithmetic computes power-series arithmetic -/






/-! ## 4. The eta product and the Eisenstein series -/


lemma deltaPart_succ (m : ℕ) :
    deltaPart (m + 1) = deltaPart m * (1 - X ^ (m + 1)) ^ 24 := by
  rw [deltaPart, deltaPart, Finset.prod_Icc_succ_top (by omega)]





/-! ## 5. Truncation stability: the eta product is well defined -/

/-- Beyond degree `k`, the factor `(1 - q^k)^24` is invisible. -/
lemma agree_etaFactor_one {N k : ℕ} (hk : N ≤ k) :
    AgreeBelow N ((1 - X ^ k) ^ 24) 1 := by
  rw [agreeBelow_iff_dvd]
  have hdvd : ((1 : PowerSeries ℤ) - X ^ k) - 1 ∣ (1 - X ^ k) ^ 24 - 1 ^ 24 :=
    sub_dvd_pow_sub_pow _ _ 24
  have hsimp : ((1 : PowerSeries ℤ) - X ^ k) - 1 = -(X ^ k) := by ring
  rw [hsimp, one_pow] at hdvd
  refine dvd_trans (pow_dvd_pow (X : PowerSeries ℤ) hk) (dvd_trans ?_ hdvd)
  exact (dvd_neg).mpr dvd_rfl

/-- Adding one more factor does not change the coefficients below degree `N`,
once the factor's exponent has passed `N`. -/
lemma deltaPart_succ_agree {N m : ℕ} (h : N ≤ m + 1) :
    AgreeBelow N (deltaPart (m + 1)) (deltaPart m) := by
  rw [deltaPart_succ]
  simpa using (AgreeBelow.refl N (deltaPart m)).mul (agree_etaFactor_one (k := m + 1) h)

/-- **Stability of the eta product.**  The coefficients of `∏_{k≤m}(1-q^k)^24`
in degrees `< N` are independent of the cut-off `m`, as soon as `m ≥ N - 1`.
This is what makes the infinite product well defined coefficientwise. -/
theorem deltaPart_agree_of_le {N : ℕ} : ∀ m : ℕ, N ≤ m + 1 →
    AgreeBelow N (deltaPart m) (deltaPart (N - 1))
  | 0, hm => by
      have h0 : N - 1 = 0 := by omega
      rw [h0]
  | (m + 1), hm => by
      rcases Nat.lt_or_ge N (m + 2) with hlt | hge
      · exact (deltaPart_succ_agree (by omega)).trans (deltaPart_agree_of_le m (by omega))
      · have hNm : N = m + 2 := by omega
        subst hNm
        have hm1 : m + 2 - 1 = m + 1 := by omega
        rw [hm1]



/-! ## 6. The verified expansion -/





/-! ## 7. The head-table entry for the identity class -/






/-! ## 8. McKay's observation, on verified numbers

The dimensions of the smallest irreducible representations of the Monster are
`1`, `196883`, `21296876`, `842609326`, `19360062527`, `293553734298`.  The
following identities exhibit the verified `j`-coefficients as non-negative
integral combinations of them — the numerical shadow of the graded Monster
module `V♮`. -/







open MoonshineJ in
theorem solution{N m m' : ℕ} (h : N ≤ m + 1) (h' : N ≤ m' + 1) :
    AgreeBelow N (deltaPart m) (deltaPart m') :=
  (deltaPart_agree_of_le m h).trans (deltaPart_agree_of_le m' h').symm
