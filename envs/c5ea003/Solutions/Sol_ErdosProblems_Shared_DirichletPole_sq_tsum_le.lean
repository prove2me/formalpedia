-- Prove2me | solution 1 for ErdosProblems.Shared.DirichletPole.sq_tsum_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:19:50.981427+00:00
-- url     : https://prove2.me/submissions/b2f390a5-da4b-4e7d-9a69-2c62698f0bc3

import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
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

theorem LSeriesSummable_ofReal_iff (f : ℕ → ℝ) (s : ℝ) :
    LSeriesSummable (fun k => (f k : ℂ)) (s : ℂ) ↔ Summable (rterm f s) := by
  rw [LSeriesSummable, ← Complex.summable_ofReal]
  exact summable_congr fun n => term_ofReal f s n

theorem convolution_ofReal (f g : ℕ → ℝ) :
    ((fun k => (f k : ℂ)) ⍟ (fun k => (g k : ℂ))) = fun n => ((dconv f g n : ℝ) : ℂ) := by
  rw [LSeries.convolution_def]
  funext n
  simp [dconv]

theorem rterm_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (s : ℝ) (n : ℕ) :
    0 ≤ rterm f s n := by
  unfold rterm
  split_ifs
  · exact le_rfl
  · exact div_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

theorem rterm_mono {f g : ℕ → ℝ} (h : ∀ n, n ≠ 0 → f n ≤ g n) (s : ℝ) (n : ℕ) :
    rterm f s n ≤ rterm g s n := by
  unfold rterm
  split_ifs with hn
  · exact le_rfl
  · exact div_le_div_of_nonneg_right (h n hn) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

theorem rterm_le_div {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    rterm f s n ≤ f n / n := by
  unfold rterm
  split_ifs with hn
  · subst hn
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (n : ℝ) ≤ (n : ℝ) ^ s := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le hn1 hs
    exact div_le_div_of_nonneg_left (hf n) (by linarith) hpow

/-- The real Dirichlet series of a convolution is the product of the two series. -/
theorem summable_and_tsum_rterm_dconv {f g : ℕ → ℝ} {s : ℝ}
    (hf : Summable (rterm f s)) (hg : Summable (rterm g s)) :
    Summable (rterm (dconv f g) s) ∧
      ∑' n, rterm (dconv f g) s n = (∑' n, rterm f s n) * (∑' n, rterm g s n) := by
  have hf' : LSeriesSummable (fun k => (f k : ℂ)) (s : ℂ) :=
    (LSeriesSummable_ofReal_iff f s).mpr hf
  have hg' : LSeriesSummable (fun k => (g k : ℂ)) (s : ℂ) :=
    (LSeriesSummable_ofReal_iff g s).mpr hg
  have hconv := LSeries_convolution' hf' hg'
  have hsum := LSeriesSummable.convolution hf' hg'
  rw [convolution_ofReal] at hconv hsum
  refine ⟨(LSeriesSummable_ofReal_iff _ s).mp hsum, ?_⟩
  rw [LSeries_ofReal, LSeries_ofReal, LSeries_ofReal] at hconv
  exact_mod_cast hconv
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
    {s : ℝ} (hs : 1 ≤ s) (hsa : Summable (rterm a s)) (hsm : Summable (rterm m s)) :
    (∑' n, rterm a s n) ^ 2 ≤ B ^ 2 * ∑' n, rterm m s n := by
  have hsg : Summable (rterm g s) :=
    Summable.of_nonneg_of_le (rterm_nonneg hg s)
      (fun n => rterm_mono (fun k _ => hga k) s n) hsa
  have hdivnn : ∀ n, 0 ≤ b n / (n : ℝ) := fun n => div_nonneg (hb n) (Nat.cast_nonneg n)
  have hsdiv : Summable (fun n => b n / (n : ℝ)) := summable_of_sum_range_le hdivnn h3
  have hsb : Summable (rterm b s) :=
    Summable.of_nonneg_of_le (rterm_nonneg hb s) (rterm_le_div hb hs) hsdiv
  have hBs : ∑' n, rterm b s n ≤ B :=
    (Summable.tsum_le_tsum (rterm_le_div hb hs) hsb hsdiv).trans
      (Real.tsum_le_of_sum_range_le hdivnn h3)
  obtain ⟨hsgb, hgb⟩ := summable_and_tsum_rterm_dconv hsg hsb
  obtain ⟨hsgg, hgg⟩ := summable_and_tsum_rterm_dconv hsg hsg
  have hA_le : ∑' n, rterm a s n ≤ ∑' n, rterm (dconv g b) s n :=
    Summable.tsum_le_tsum (rterm_mono h1 s) hsa hsgb
  have hGG_le : ∑' n, rterm (dconv g g) s n ≤ ∑' n, rterm m s n :=
    Summable.tsum_le_tsum (rterm_mono h2 s) hsgg hsm
  have hA0 : 0 ≤ ∑' n, rterm a s n := tsum_nonneg (rterm_nonneg ha s)
  have hG0 : 0 ≤ ∑' n, rterm g s n := tsum_nonneg (rterm_nonneg hg s)
  have hB0 : 0 ≤ B := by simpa using h3 0
  rw [hgb] at hA_le
  rw [hgg] at hGG_le
  have hAGB : ∑' n, rterm a s n ≤ (∑' n, rterm g s n) * B :=
    hA_le.trans (mul_le_mul_of_nonneg_left hBs hG0)
  calc (∑' n, rterm a s n) ^ 2 ≤ ((∑' n, rterm g s n) * B) ^ 2 :=
        pow_le_pow_left₀ hA0 hAGB 2
    _ = B ^ 2 * ((∑' n, rterm g s n) * (∑' n, rterm g s n)) := by ring
    _ ≤ B ^ 2 * ∑' n, rterm m s n := mul_le_mul_of_nonneg_left hGG_le (sq_nonneg B)
