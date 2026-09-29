-- Prove2me | solution 1 for SubgroupExtremals.mem_image_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:22:47.856869+00:00
-- url     : https://prove2.me/submissions/5d063db8-fc2a-4ab7-96bd-ec558993f381

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
theorem solution(ha : a ≠ 0) (hN : N = a * b) (j : ZMod N) :
    j ∈ (Finset.range b).image (fun t => ((a * t : ℕ) : ZMod N)) ↔ a ∣ j.val := by
  constructor
  · intro h
    simp only [Finset.mem_image, Finset.mem_range] at h
    obtain ⟨t, ht, rfl⟩ := h
    have hlt : a * t < N := by
      rw [hN]; exact (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero ha)).2 ht
    rw [ZMod.val_natCast_of_lt hlt]
    exact Dvd.intro t rfl
  · intro h
    obtain ⟨t, ht⟩ := h
    have hval : j.val < N := ZMod.val_lt j
    have htb : t < b := by
      rw [ht, hN] at hval
      exact lt_of_mul_lt_mul_left hval (Nat.zero_le a)
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨t, htb, by rw [← ht]; simp⟩
