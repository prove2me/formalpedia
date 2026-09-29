-- Prove2me | solution 1 for ProfileForm.exp_lt_pade
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:31:00.867269+00:00
-- url     : https://prove2.me/submissions/b94e1e42-84bc-4993-9aa1-f9ee5c217d4b

-- Sol generated from NumberTheory/ProfileFormHumpThreshold.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormHumpLocation
import Definitions.Def_NumberTheory_ProfileFormHumpThreshold
import Definitions.Def_NumberTheory_ProfileFormUniformMixturePeak

/-!
# Profile form IX: a critical exponent for the mixture hump

`ProfileFormUniformMixturePeak` proved that the residual of the power law
`T(x) = (1+x)^{-b}` against the uniform Dickman surrogate
`M(x) = (1 - e^{-x})/x` really does hump, for the measured exponent
`b = 11/10`, at `x ≈ 10`.  `ProfileFormHumpLocation` then explained the location
via the exact maximiser `x* = 1/(b-1)` of the elementary factor
`x (1+x)^{-b}`.

Both results leave open whether the hump is a *universal* feature of this
profile/baseline pair.  It is not.  The exact logarithmic derivative is

  `d/dx log (T/M)(x) = 1/x - b/(1+x) - 1/(e^x - 1)`,

so the hump is a competition between the algebraic term `1/x - b/(1+x)`, which
is positive up to `x* = 1/(b-1)`, and the exponential correction `1/(e^x - 1)`,
which is large exactly where `x` is small.  As `b` increases, `x*` shrinks into
the region where the correction dominates and the hump is destroyed.

Here we prove the destruction side rigorously:

* `exp_lt_pade` — the Padé bound `e^x < (2+x)/(2-x)` on `(0,2)`;
* `one_div_exp_sub_one_gt` — hence `1/x - 1/2 < 1/(e^x - 1)` for all `x > 0`;
* `uniformMixtureResidual_strictAntiOn` — **for every `b ≥ 3/2` the residual
  `T/M` is strictly decreasing on all of `(0,∞)`: no hump anywhere**;
* `uniform_hump_regime_bracket` — combined with the proved hump at `b = 11/10`,
  the humping regime is bracketed: it holds at `11/10` and fails from `3/2` on,
  so a critical exponent lies in `(11/10, 3/2)`.  Numerically it is
  `b_c ≈ 1.1605`, and the reported bootstrap interval `[0.991, 1.218]` straddles
  it — a second, independent way in which the experiment does not settle the
  qualitative shape.

The constant `3/2` is exactly what the two elementary bounds give: the argument
needs `1/(b-1) ≤ 2 ≤ 2b - 1`, i.e. `2b² - 3b ≥ 0`.
-/

open ProfileForm

open Set Filter Topology




/-! ### The log-residual and its derivative -/









open ProfileForm in
theorem solution{x : ℝ} (hx : 0 < x) (hx2 : x < 2) : Real.exp x < (2 + x) / (2 - x) := by
  set h : ℝ → ℝ := fun t => (2 + t) * Real.exp (-t) - (2 - t) with hh
  have hderiv : ∀ t : ℝ, HasDerivAt h (1 - (1 + t) * Real.exp (-t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => 2 + s) 1 t := by simpa using (hasDerivAt_id t).const_add 2
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
    have h3 : HasDerivAt (fun s : ℝ => 2 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 2
    have hsum := (h1.mul h2).sub h3
    convert hsum using 1
    ring
  have hmono : StrictMonoOn h (Ici (0:ℝ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _)
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    rw [(hderiv t).deriv]
    have hlt : (1 + t) * Real.exp (-t) < 1 := by
      have hpos : (0:ℝ) < Real.exp t := Real.exp_pos t
      have h1t : 1 + t < Real.exp t := by
        have := Real.add_one_lt_exp (x := t) (by simp only [mem_Ioi] at ht; linarith)
        linarith
      rw [Real.exp_neg, mul_inv_lt_iff₀ hpos]
      linarith
    linarith
  have h0 : h 0 = 0 := by simp [hh]
  have hpos : 0 < h x := by
    have := hmono (mem_Ici.mpr (le_refl (0:ℝ))) (mem_Ici.mpr hx.le) hx
    rw [h0] at this; exact this
  have hexp : (2 - x) < (2 + x) * Real.exp (-x) := by simpa [hh] using hpos
  rw [lt_div_iff₀ (by linarith), mul_comm]
  rw [Real.exp_neg] at hexp
  calc (2 - x) * Real.exp x < ((2 + x) * (Real.exp x)⁻¹) * Real.exp x :=
        mul_lt_mul_of_pos_right hexp (Real.exp_pos x)
    _ = 2 + x := by field_simp
