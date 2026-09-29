-- Prove2me | solution 1 for SmoothWindows.gaussSum_summable_of_sq_growth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:51:04.392816+00:00
-- url     : https://prove2.me/submissions/0bafbee3-62c2-4478-b34a-a4d35b6144d7

-- Sol generated from Algebra/SmoothWindows/SchwartzDecay.lean
import Mathlib
import Definitions.Def_Algebra_SmoothWindows_GaussianWindow
import Theorems.Thm_SmoothWindows_gaussWin_pos
import Theorems.Thm_SmoothWindows_gaussWin_sq_pow_mul_le

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


/-- The Gaussian window is bounded by any inverse power of `t²`. -/
theorem gaussWin_le_div_sq_pow {s : ℝ} (hs : s ≠ 0) (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    gaussWin s t ≤ (s ^ 2 / π) ^ n * n.factorial / (t ^ 2) ^ n := by
  have hpos : (0:ℝ) < (t ^ 2) ^ n := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  exact gaussWin_sq_pow_mul_le hs n t



/-! ## Gaussian regularisation of infinite ordinate families -/




open SmoothWindows in
theorem solution{s : ℝ} (hs : s ≠ 0) (t : ℕ → ℝ)
    (ht : ∀ k : ℕ, ((k : ℝ) + 1) ≤ (t k) ^ 2) :
    Summable fun k => gaussWin s (t k) / (1 / 4 + (t k) ^ 2) := by
  set M : ℝ := (s ^ 2 / π) ^ 2 * (Nat.factorial 2) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hcomp : Summable fun k : ℕ => 4 * M * (1 / ((k : ℝ) + 1) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h
    exact ((by simpa using h1 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hcomp
  · have : (0:ℝ) < 1 / 4 + (t k) ^ 2 := by positivity
    have := gaussWin_pos s (t k)
    positivity
  · have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
    have hsq : ((k : ℝ) + 1) ≤ (t k) ^ 2 := ht k
    have htk : (t k) ≠ 0 := by
      intro h
      rw [h] at hsq
      simp at hsq
      linarith [hsq]
    have hbound : gaussWin s (t k) ≤ M / ((t k) ^ 2) ^ 2 :=
      gaussWin_le_div_sq_pow hs 2 htk
    have hden : (0:ℝ) < 1 / 4 + (t k) ^ 2 := by positivity
    have hden4 : (1:ℝ) / 4 ≤ 1 / 4 + (t k) ^ 2 := by nlinarith [sq_nonneg (t k)]
    have hgw0 : 0 < gaussWin s (t k) := gaussWin_pos _ _
    have step1 : gaussWin s (t k) / (1 / 4 + (t k) ^ 2) ≤ gaussWin s (t k) / (1 / 4) := by
      apply div_le_div_of_nonneg_left hgw0.le (by norm_num) hden4
    have hpow : (((k : ℝ) + 1) ^ 2) ≤ (((t k) ^ 2)) ^ 2 := by
      have := sq_nonneg (t k)
      nlinarith [hsq, hk1]
    have hMdiv : M / ((t k) ^ 2) ^ 2 ≤ M / ((k : ℝ) + 1) ^ 2 := by
      apply div_le_div_of_nonneg_left hM0 (by positivity) hpow
    calc gaussWin s (t k) / (1 / 4 + (t k) ^ 2) ≤ gaussWin s (t k) / (1 / 4) := step1
      _ = 4 * gaussWin s (t k) := by ring
      _ ≤ 4 * (M / ((k : ℝ) + 1) ^ 2) := by linarith
      _ = 4 * M * (1 / ((k : ℝ) + 1) ^ 2) := by ring
