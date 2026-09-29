-- Prove2me | solution 1 for ErdosProblems.Shared.DirichletPole.false_of_pole_comparison
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:28:31.996029+00:00
-- url     : https://prove2.me/submissions/61aa517f-dc61-4f67-aca7-7b0109aaed26

import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Theorems.Thm_ErdosProblems_Shared_DirichletPole_sq_tsum_le
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Two simple poles exclude a squared comparison of Dirichlet series

Let `a, g, b, m : ℕ → ℝ` be nonnegative with

* `a ≤ g ⋆ b` and `g ⋆ g ≤ m` coefficientwise (Dirichlet convolution, `n ≠ 0`),
* `g ≤ a`, and the partial sums of `∑ b(n) / n` bounded by `B`.

If the Dirichlet series of `a` and of `m` both have a simple pole at `s = 1`
(`(s - 1) L(a, s) → r_a > 0` and `(s - 1) L(m, s) → r_m ≠ 0` as `s → 1⁺`), this is
impossible.  Indeed, for real `s > 1` near `1`,

`L(a, s) ^ 2 ≤ (L(g, s) L(b, s)) ^ 2 ≤ B ^ 2 L(g ⋆ g, s) ≤ B ^ 2 L(m, s)`,

so `((s - 1) L(a, s)) ^ 2 ≤ B ^ 2 (s - 1) · (s - 1) L(m, s)`; the left side tends to
`r_a ^ 2 > 0` and the right side to `0`.

This is the analytic core of the classical proof that a non-square element of a number
field is a non-square modulo infinitely many degree-one primes: `a` counts the ideals of
the base field, `m` those of the quadratic extension, `g` the ideals built from split
degree-one primes and `b` the rest.  Summability of the two series near `s = 1` is not
assumed: it follows from the nonzero limits, since a divergent series has `tsum = 0`.
-/

noncomputable section

namespace ErdosProblems.Shared.DirichletPole
open Filter Topology
open scoped LSeries.notation





theorem term_ofReal (f : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    LSeries.term (fun k => (f k : ℂ)) (s : ℂ) n = ((rterm f s n : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [rterm]
  · rw [LSeries.term_of_ne_zero hn, rterm, if_neg hn, Complex.ofReal_div,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

theorem LSeries_ofReal (f : ℕ → ℝ) (s : ℝ) :
    LSeries (fun k => (f k : ℂ)) (s : ℂ) = ((∑' n, rterm f s n : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr fun n => term_ofReal f s n















/-- The real part of `(s - 1) L(f, s)` along real `s`. -/
theorem tendsto_real_of_tendsto_LSeries {f : ℕ → ℝ} {r : ℝ}
    (h : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries (fun n => (f n : ℂ)) s)
      (𝓝[>] 1) (𝓝 (r : ℂ))) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' n, rterm f s n) (𝓝[>] 1) (𝓝 r) := by
  have h' := (Complex.continuous_re.tendsto (r : ℂ)).comp h
  rw [Complex.ofReal_re] at h'
  refine h'.congr fun s => ?_
  simp only [Function.comp_apply, LSeries_ofReal]
  rw [show ((s : ℂ) - 1) * ((∑' n, rterm f s n : ℝ) : ℂ)
      = (((s - 1) * ∑' n, rterm f s n : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
end ErdosProblems.Shared.DirichletPole

open Filter Topology
open scoped LSeries.notation
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.DirichletPole in
theorem solution {a g b m : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hg : ∀ n, 0 ≤ g n) (hb : ∀ n, 0 ≤ b n)
    (hga : ∀ n, g n ≤ a n)
    (h1 : ∀ n, n ≠ 0 → a n ≤ dconv g b n)
    (h2 : ∀ n, n ≠ 0 → dconv g g n ≤ m n)
    (B : ℝ) (h3 : ∀ X : ℕ, ∑ n ∈ Finset.range X, b n / n ≤ B)
    {ra rm : ℝ} (hra : 0 < ra) (hrm : rm ≠ 0)
    (hA : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries (fun n => (a n : ℂ)) s)
      (𝓝[>] 1) (𝓝 (ra : ℂ)))
    (hM : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries (fun n => (m n : ℂ)) s)
      (𝓝[>] 1) (𝓝 (rm : ℂ))) :
    False := by
  have hA' := tendsto_real_of_tendsto_LSeries hA
  have hM' := tendsto_real_of_tendsto_LSeries hM
  have hAev := hA'.eventually_ne hra.ne'
  have hMev := hM'.eventually_ne hrm
  have hkey : ∀ᶠ s in 𝓝[>] (1 : ℝ),
      ((s - 1) * ∑' n, rterm a s n) ^ 2 ≤
        B ^ 2 * (s - 1) * ((s - 1) * ∑' n, rterm m s n) := by
    filter_upwards [hAev, hMev, self_mem_nhdsWithin] with s hAs hMs hs1
    have hs1' : (1 : ℝ) < s := hs1
    have hsa : Summable (rterm a s) := by
      by_contra hns
      exact hAs (by rw [tsum_eq_zero_of_not_summable hns, mul_zero])
    have hsm : Summable (rterm m s) := by
      by_contra hns
      exact hMs (by rw [tsum_eq_zero_of_not_summable hns, mul_zero])
    have hsq := sq_tsum_le ha hg hb hga h1 h2 B h3 hs1'.le hsa hsm
    have hs0 : 0 ≤ (s - 1) ^ 2 := sq_nonneg _
    calc ((s - 1) * ∑' n, rterm a s n) ^ 2 = (s - 1) ^ 2 * (∑' n, rterm a s n) ^ 2 := by ring
      _ ≤ (s - 1) ^ 2 * (B ^ 2 * ∑' n, rterm m s n) := mul_le_mul_of_nonneg_left hsq hs0
      _ = B ^ 2 * (s - 1) * ((s - 1) * ∑' n, rterm m s n) := by ring
  have hlim0 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have h := ((continuous_id.sub continuous_const).tendsto (1 : ℝ) :
      Tendsto (fun s : ℝ => id s - 1) (𝓝 1) (𝓝 (id 1 - 1)))
    simpa using h
  have hR : Tendsto (fun s : ℝ => B ^ 2 * (s - 1) * ((s - 1) * ∑' n, rterm m s n))
      (𝓝[>] 1) (𝓝 (B ^ 2 * 0 * rm)) :=
    (hlim0.const_mul (B ^ 2)).mul hM'
  have hL : Tendsto (fun s : ℝ => ((s - 1) * ∑' n, rterm a s n) ^ 2) (𝓝[>] 1) (𝓝 (ra ^ 2)) :=
    hA'.pow 2
  have hle := le_of_tendsto_of_tendsto hL hR hkey
  have hpos : 0 < ra ^ 2 := pow_pos hra 2
  simp at hle
  linarith
