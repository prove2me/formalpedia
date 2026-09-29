-- Prove2me | solution 1 for SubgroupExtremals.dft_indicator_apply
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:27:37.515303+00:00
-- url     : https://prove2.me/submissions/8e025644-2ba8-4ad7-ac10-f549ab378f2b

-- Sol generated from Bridges/SubgroupExtremals.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_SubgroupExtremals
import Theorems.Thm_SubgroupExtremals_dft_indicator_eq_geom

/-!
# Subgroup indicators are the extremals of the Donoho–Stark bound

The previous file proved the Donoho–Stark uncertainty principle
`N ≤ |supp Φ| * |supp 𝓕Φ|` on `ZMod N`, showed it is attained by delta functions, and exhibited
one composite counterexample (`N = 4`) to the additive prime bound. This file proves the general
structural statement behind that counterexample.

For every factorisation `N = d * m` the indicator function of the subgroup of multiples of `d`
has support of size `m`, and its discrete Fourier transform is the indicator of the subgroup of
multiples of `m` scaled by `m`, hence has support of size `d`. Consequently:

* `SubgroupExtremals.donoho_stark_extremal` : the Donoho–Stark bound is attained with equality by
  the whole family of subgroup indicators, `|supp Φ| * |supp 𝓕Φ| = N`;
* `SubgroupExtremals.additive_bound_le_divisor_sum` : the additive support sum equals `d + m`,
  so the prime (Tao) bound `N + 1` fails for every composite `N`;
* `SubgroupExtremals.tao_bound_fails_of_composite` : an explicit statement of that failure.

The proof is a genuine finite Fourier computation: the transform of the indicator is a geometric
sum of a root of unity, which vanishes off the annihilator subgroup.
-/

open Finset ZMod FourierUncertainty

open SubgroupExtremals

/-! ## Counting the multiples of `a` in `ZMod (a * b)` -/


variable {N a b : ℕ} [NeZero N]




/-! ## The indicator of a subgroup and its Fourier transform -/


variable (d m : ℕ) [NeZero d] [NeZero m]




variable {d m}





/-- The `m`-th power of the relevant root of unity is one. -/
theorem char_pow_eq_one (k : ZMod (d * m)) :
    (stdAddChar (-((d : ZMod (d * m)) * k))) ^ m = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  have : (m : ℕ) • (-((d : ZMod (d * m)) * k)) = 0 := by
    rw [nsmul_eq_mul,
      show ((m : ZMod (d * m)) * -((d : ZMod (d * m)) * k))
        = -(((d * m : ℕ) : ZMod (d * m)) * k) by push_cast; ring,
      ZMod.natCast_self, zero_mul, neg_zero]
  rw [this, AddChar.map_zero_eq_one]











open SubgroupExtremals in
theorem solution(k : ZMod (d * m)) :
    𝓕 (indicator d m) k = if (d : ZMod (d * m)) * k = 0 then (m : ℂ) else 0 := by
  classical
  rw [dft_indicator_eq_geom]
  set z : ℂ := stdAddChar (-((d : ZMod (d * m)) * k)) with hz
  by_cases hk : (d : ZMod (d * m)) * k = 0
  · have hz1 : z = 1 := by rw [hz, hk, neg_zero, AddChar.map_zero_eq_one]
    simp [hz1, hk]
  · have hz1 : z ≠ 1 := by
      rw [hz]
      intro h
      apply hk
      have := ZMod.injective_stdAddChar (N := d * m) (by
        rw [h, AddChar.map_zero_eq_one] : stdAddChar (-((d : ZMod (d * m)) * k))
          = stdAddChar 0)
      simpa using this
    rw [geom_sum_eq hz1, char_pow_eq_one k]
    simp [hk]
