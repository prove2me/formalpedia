-- Prove2me | solution 1 for SmoothWindows.gaussWin_sq_pow_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:31:28.481006+00:00
-- url     : https://prove2.me/submissions/a3cf1b9a-a4f8-422e-bc6f-1cebf246715a

-- Sol generated from Algebra/SmoothWindows/SchwartzDecay.lean
import Mathlib
import Definitions.Def_Algebra_SmoothWindows_GaussianWindow

/-!
# Smooth windows VII: Schwartz-type decay and Gaussian regularisation of infinite zero families

Cycle 4 of the programme.  Everything proved so far concerned *finite* multisets of ordinates,
because that is what the catalog's `windowSum` is defined on.  The point of a **Schwartz** window,
as opposed to a merely bounded one, is that it makes infinite families summable.  This file makes
that precise and quantitative.

## Main results

* `gaussWin_sq_pow_mul_le` — the **explicit Schwartz bound**
  `(t²)ⁿ · g_s(t) ≤ (s²/π)ⁿ · n!` for every `n` and every `t`, with an explicit constant.  This is
  the exponential-series inequality `yⁿ/n! ≤ eʸ` transported through the substitution
  `y = π t²/s²`; it is the reason the Gaussian window has finite seminorms of every order.
* `gaussWin_abs_pow_mul_le` — the same statement for arbitrary (not necessarily even) powers,
  `|t|ᵐ · g_s(t) ≤ 1 + (s²/π)ᵐ · m!`.
* `gaborAtom_decay_uniform` — the decay constant is **uniform over the whole Heisenberg orbit**:
  for every phase-space point `(a, b)`, `|t - a|ᵐ · ‖gaborAtom s a b t‖` obeys the *same* bound.
  The orbit of the Gaussian under the group `Heis` of `Algebra.SmoothWindows.GaborOperators` is a
  bounded family of Schwartz-type windows, which is exactly the property that the Weyl identity
  `SmoothWindows.modOp_transOp` alone does not give.
* `gaussSum_summable_of_sq_growth` — **Gaussian regularisation.**  If the ordinates satisfy only
  the square-root growth condition `k + 1 ≤ t_k²`, the Gaussian-windowed harmonic series
  `Σ_k g_s(t_k)/(1/4 + t_k²)` converges absolutely.
* `harmonic_not_summable_sqrt_ordinates` — and the hypothesis is **sharp in the sense that it does
  not suffice without the window**: for `t_k = √(k+1)`, which satisfies the growth condition with
  equality, the *unwindowed* harmonic series `Σ_k 1/(1/4 + t_k²)` diverges.  So on this family the
  Gaussian window converts a divergent catalog statistic into a convergent one — something no
  bounded-below window (and in particular no rectangular window of infinite width) can do.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).** Conjecture: the Gaussian window is not merely a smoother
  rectangular window but a *regulariser*, extending the catalog's harmonic statistic from finite
  multisets to infinite families whose harmonic sum diverges.  Bold form: there is a growth
  threshold at which the two windows disagree about whether the statistic exists at all.
* **Experiment (Experimenter).** The threshold was found by pushing the exponential bound
  `yⁿ ≤ n! eʸ` to arbitrary `n`: it gives `g_s(t) ≤ Cₙ/(t²)ⁿ` for *every* `n`, so the Gaussian beats
  every polynomial.  Setting `t_k² = k + 1` makes the unwindowed terms `1/(k + 5/4)`, the harmonic
  series, while the windowed terms are `O(1/(k+1)²)` already at `n = 2`.  Numerically with `s = 1`:
  `Σ_{k<10⁴} 1/(k + 5/4) ≈ 9.4379` and still growing like `log k`, whereas
  `Σ_{k<10⁴} g_1(√(k+1))/(k + 5/4) ≈ 0.035427`, already constant to five digits past `k = 3`.
* **Analysis (Analyst).** The mechanism is that the constant `Cₙ = (s²/π)ⁿ n!` grows with `n` but is
  independent of `t`: for fixed `s` one may choose `n` *after* seeing the growth exponent of the
  family.  This is precisely the quantifier order that a rectangular window cannot reproduce, since
  its transfer function has a fixed polynomial decay rate `1/ξ`
  (`SmoothWindows.norm_fourier_rectWin_sidelobeFreq`).
* **Critique (Critic).** Two traps were checked.  (i) `gaussWin_abs_pow_mul_le` cannot drop the
  `1 +`.  The function `|t|ᵐ g_s(t)` is maximised at `|t| = s√(m/2π)`; for `m = 1`, `s = 1/2` its
  maximum is `0.12099`, whereas the pure power bound would assert `≤ (s²/π)¹·1! = 0.07958`.  The
  pure bound therefore fails for every `s < 0.76` at `m = 1`, and the additive `1` is the cheapest
  uniform fix.  (ii) The divergence statement is about the *specific* family `√(k+1)` and
  is proved by comparison with the harmonic series, not asserted in general — a family with
  `t_k² ≥ k+1` growing faster would of course have a convergent unwindowed sum too.
-/

open SmoothWindows

open Complex Real Filter Topology

/-! ## The explicit Schwartz bound for the Gaussian window -/





/-! ## Gaussian regularisation of infinite ordinate families -/




open SmoothWindows in
theorem solution{s : ℝ} (hs : s ≠ 0) (n : ℕ) (t : ℝ) :
    (t ^ 2) ^ n * gaussWin s t ≤ (s ^ 2 / π) ^ n * n.factorial := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hs2 : (0:ℝ) < s ^ 2 := by positivity
  set y : ℝ := π * t ^ 2 / s ^ 2 with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hgw : gaussWin s t = Real.exp (-y) := by
    unfold gaussWin
    congr 1
    rw [hy]
    ring
  have ht2 : t ^ 2 = s ^ 2 / π * y := by
    rw [hy]
    field_simp
  have hfac : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hexp : y ^ n ≤ n.factorial * Real.exp y := by
    have h := Real.pow_div_factorial_le_exp y hy0 n
    rw [div_le_iff₀ hfac] at h
    linarith
  have hE : (0:ℝ) < Real.exp (-y) := Real.exp_pos _
  have hcoef : (0:ℝ) ≤ (s ^ 2 / π) ^ n := by positivity
  calc (t ^ 2) ^ n * gaussWin s t
      = (s ^ 2 / π) ^ n * (y ^ n * Real.exp (-y)) := by
        rw [hgw, ht2, mul_pow]; ring
    _ ≤ (s ^ 2 / π) ^ n * ((n.factorial * Real.exp y) * Real.exp (-y)) := by
        gcongr
    _ = (s ^ 2 / π) ^ n * n.factorial := by
        rw [mul_assoc, ← Real.exp_add]
        simp
