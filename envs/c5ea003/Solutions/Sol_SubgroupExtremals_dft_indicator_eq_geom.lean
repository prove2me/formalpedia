-- Prove2me | solution 1 for SubgroupExtremals.dft_indicator_eq_geom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:24:50.556308+00:00
-- url     : https://prove2.me/submissions/8b6f73fa-f45e-49a3-8f58-140351eb7150

-- Sol generated from Bridges/SubgroupExtremals.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_SubgroupExtremals

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
















open SubgroupExtremals in
theorem solution(k : ZMod (d * m)) :
    𝓕 (indicator d m) k
      = ∑ t ∈ Finset.range m, (stdAddChar (-((d : ZMod (d * m)) * k))) ^ t := by
  classical
  rw [ZMod.dft_apply]
  have hsum : ∑ j : ZMod (d * m), stdAddChar (-(j * k)) • indicator d m j
      = ∑ j ∈ multiples d m, stdAddChar (-(j * k)) • indicator d m j := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    simp [indicator, hx]
  rw [hsum, multiples, Finset.sum_image]
  · refine Finset.sum_congr rfl fun t ht => ?_
    have hmem : ((d * t : ℕ) : ZMod (d * m)) ∈ multiples d m := by
      simp only [multiples, Finset.mem_image]
      exact ⟨t, ht, rfl⟩
    rw [show indicator d m ((d * t : ℕ) : ZMod (d * m)) = 1 from if_pos hmem]
    rw [smul_eq_mul, mul_one]
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    push_cast
    ring
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_range] at hx hy
    have h : (d * x) ≡ (d * y) [MOD d * m] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hxy
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.mul_left_cancel' (NeZero.ne d) h) hx hy
