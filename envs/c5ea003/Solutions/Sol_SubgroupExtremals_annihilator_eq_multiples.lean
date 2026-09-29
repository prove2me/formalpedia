-- Prove2me | solution 1 for SubgroupExtremals.annihilator_eq_multiples
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:24:49.987074+00:00
-- url     : https://prove2.me/submissions/9d601657-e915-45e2-93f3-408f4b27f4c3

-- Sol generated from Bridges/SubgroupExtremals.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_SubgroupExtremals
import Theorems.Thm_SubgroupExtremals_mem_image_mul_iff

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
theorem solution:
    (Finset.univ.filter fun k : ZMod (d * m) => (d : ZMod (d * m)) * k = 0)
      = (Finset.range d).image (fun t => ((m * t : ℕ) : ZMod (d * m))) := by
  classical
  ext k
  rw [mem_image_mul_iff (NeZero.ne m) (mul_comm d m) k]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have hcast : (((d * k.val : ℕ)) : ZMod (d * m)) = 0 := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
      exact h
    have hdvd : (d * m) ∣ d * k.val := (ZMod.natCast_eq_zero_iff _ _).1 hcast
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, ?_⟩
    have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have : d * (m * c) = d * k.val := by rw [hc]; ring
    exact (Nat.eq_of_mul_eq_mul_left hd this).symm
  · rintro ⟨c, hc⟩
    have hcast : (((d * k.val : ℕ)) : ZMod (d * m)) = 0 := by
      rw [hc, show d * (m * c) = (d * m) * c by ring, Nat.cast_mul, ZMod.natCast_self,
        zero_mul]
    have : (d : ZMod (d * m)) * k = ((d * k.val : ℕ) : ZMod (d * m)) := by
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [this, hcast]
