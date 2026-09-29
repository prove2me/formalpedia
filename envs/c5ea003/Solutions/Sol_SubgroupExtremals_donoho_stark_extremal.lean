-- Prove2me | solution 1 for SubgroupExtremals.donoho_stark_extremal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:29:07.386785+00:00
-- url     : https://prove2.me/submissions/98825d24-fd97-463f-96b7-fa4a7b38491b

-- Sol generated from Bridges/SubgroupExtremals.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_SubgroupExtremals
import Theorems.Thm_FourierUncertainty_mem_fsupport
import Theorems.Thm_SubgroupExtremals_annihilator_eq_multiples
import Theorems.Thm_SubgroupExtremals_dft_indicator_apply

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


omit [NeZero N] in
/-- There are exactly `b` multiples of `a` in `ZMod (a * b)`. -/
theorem card_image_mul (ha : a ≠ 0) (hN : N = a * b) :
    ((Finset.range b).image (fun t => ((a * t : ℕ) : ZMod N))).card = b := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_range] at hx hy
  have h : (a * x) ≡ (a * y) [MOD N] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hxy
  rw [hN] at h
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.mul_left_cancel' ha h) hx hy


/-! ## The indicator of a subgroup and its Fourier transform -/


variable (d m : ℕ) [NeZero d] [NeZero m]




variable {d m}

omit [NeZero m] in
theorem card_multiples : (multiples d m).card = m :=
  card_image_mul (NeZero.ne d) rfl

theorem fsupport_indicator : fsupport (indicator d m) = multiples d m := by
  classical
  ext j
  simp only [mem_fsupport, indicator]
  by_cases h : j ∈ multiples d m <;> simp [h]

theorem card_fsupport_indicator : (fsupport (indicator d m)).card = m := by
  rw [fsupport_indicator, card_multiples]




theorem fsupport_dft_indicator :
    fsupport (𝓕 (indicator d m)) = Finset.univ.filter fun k => (d : ZMod (d * m)) * k = 0 := by
  classical
  ext k
  simp only [mem_fsupport, Finset.mem_filter, Finset.mem_univ, true_and, dft_indicator_apply]
  by_cases hk : (d : ZMod (d * m)) * k = 0
  · simp [hk, NeZero.ne m]
  · simp [hk]


theorem card_fsupport_dft_indicator : (fsupport (𝓕 (indicator d m))).card = d := by
  rw [fsupport_dft_indicator, annihilator_eq_multiples]
  exact card_image_mul (NeZero.ne m) (mul_comm d m)







open SubgroupExtremals in
theorem solution:
    (fsupport (indicator d m)).card * (fsupport (𝓕 (indicator d m))).card = d * m := by
  rw [card_fsupport_indicator, card_fsupport_dft_indicator, Nat.mul_comm]
