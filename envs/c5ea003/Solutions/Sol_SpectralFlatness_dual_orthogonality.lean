-- Prove2me | solution 1 for SpectralFlatness.dual_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:33:28.95893+00:00
-- url     : https://prove2.me/submissions/6d7a9e6b-3463-46aa-bbcc-69c2909a4ecb

-- Sol generated from Novelty/WalshSpectralFlatness.lean
import Mathlib
import Definitions.Def_Novelty_WalshSpectralFlatness
/-
# Walsh spectra of Boolean functions: flatness, the noise floor, and the 1/2 barrier

This file develops, from scratch, the Walsh/Fourier analysis of real-valued functions on the
Boolean cube `Fin n → Bool` that is needed to state and prove the *spectral face* of the
factoring-barrier framework (Paper 53, Experiment 388).  Nothing here is specific to factoring;
the arithmetic input lives in `Novelty.SpectralFlatnessFactoring`, which imports this file.

## Main results

* `SpectralFlatness.sum_walshChar` — the character sum `∑ x, χ_S x` is `2^n` for `S = ∅` and `0`
  otherwise.
* `SpectralFlatness.walshChar_mul` — `χ_S · χ_T = χ_{S Δ T}`: the characters form a group under
  pointwise multiplication, indexed by `(Finset (Fin n), Δ)`.
* `SpectralFlatness.orthogonality` — `∑ x, χ_S x χ_T x = 2^n [S = T]`.
* `SpectralFlatness.dual_orthogonality` — `∑_S χ_S x χ_S y = 2^n [x = y]`.
* `SpectralFlatness.parseval` — `∑_S (Ŵf S)^2 = 2^n ∑_x f x ^ 2`, and
  `SpectralFlatness.parseval_corr` — `∑_S corr(f,S)^2 = 1` for sign-valued `f`.
* `SpectralFlatness.agreement_corr` — the *dictionary*: a parity `χ_S` agrees with `f` on exactly
  `2^{n-1}(1 + corr(f,S))` points.  Correlation and prediction advantage are the same quantity.
* `SpectralFlatness.agreement_le_of_corr_le` — **the 1/2 barrier.**  If every parity in a family
  has correlation at most `ε`, no parity of that family predicts `f` on more than a
  `(1+ε)/2` fraction of the cube.
* `SpectralFlatness.exists_corr_sq_ge` — **the noise floor.**  *Some* parity always achieves
  `|corr| ≥ 2^{-n/2}`: a genuinely flat spectrum is flat exactly at the noise floor, never below.
* `SpectralFlatness.card_large_corr_le` — at most `ε^{-2}` parities can have `|corr| ≥ ε`.
* `SpectralFlatness.card_support_ge_of_flat` — **spectral spreading.**  A spectrum uniformly
  bounded by `ε` must be supported on at least `ε^{-2}` parities.
* `SpectralFlatness.lowDegree_mass_le` — the Fourier mass carried by parities of degree `≤ d` is
  at most `ε²` times the number of such parities, so if that count times `ε²` is `< 1` the
  function provably has most of its mass on high-degree parities.
* `SpectralFlatness.card_lowDegree` — `|{S : |S| ≤ d}| = ∑_{i ≤ d} C(n,i)`, the size of the
  degree-`≤ d` scan performed in the experiment.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the empirical "spectral flatness" of the factoring bit-functions is not
an accident of the sample: any function whose degree-`≤ 3` correlations sit at the random-sign
null level must have its entire Fourier mass on high-degree coefficients, and no function can be
flat *below* the `2^{-n/2}` floor.

Experiment (Experimenter): the reported numbers at `k = 14` (`m = 380628` support points) are
max degree-`≤ 3` correlation `≤ 0.021`, all-parity noise `0.0101 ≈ m^{-1/2}`, degree-`≤ 3`
null max `0.0065`.  Since `m^{-1/2} = 0.00162`, `exists_corr_sq_ge` predicts a floor of that order
and the observed all-parity max is `6.2 m^{-1/2}` — exactly the `√(2 log #parities)` scaling of a
maximum of `2^n` near-independent Gaussians.  The degree-`≤ 3` scan touches
`card_lowDegree` = `1 + 28 + 378 + 3276 = 3683` parities at `n = 28`.

Analysis (Analyst): `parseval_corr` forces `∑ corr² = 1`; `card_large_corr_le` then caps the number
of ε-heavy parities at `ε^{-2}`.  With `ε = 0.021` that cap is `2267 < 3683`, so flatness at the
observed level is *consistent* with — but does not by itself imply — mass escaping to high degree;
`lowDegree_mass_le` supplies the missing quantitative step.

Critique (Critic): all of the above is an *unconditional* statement about the cube with the uniform
measure.  The experiment samples the prime-restricted semiprime support, which is neither the full
cube nor uniform, so these theorems bound the *idealised* spectrum only.  The companion file
therefore proves an exact, support-honest vanishing theorem instead of appealing to this one.
-/

open SpectralFlatness

open Finset

variable {n : ℕ}

/-! ### Signs and characters -/



theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]












/-! ### Walsh coefficients and Parseval -/







/-! ### Correlation is prediction advantage: the 1/2 barrier -/






/-! ### Flatness: the noise floor, few heavy coefficients, spectral spreading -/





/-! ### Low-degree scans -/






open SpectralFlatness in
theorem solution(x y : Fin n → Bool) :
    ∑ S ∈ (univ : Finset (Fin n)).powerset, walshChar S x * walshChar S y
      = if x = y then 2 ^ n else 0 := by
  have key : ∀ S : Finset (Fin n), walshChar S x * walshChar S y
      = ∏ i ∈ S, (sgn (x i) * sgn (y i)) := by
    intro S; rw [walshChar, walshChar, ← Finset.prod_mul_distrib]
  simp_rw [key]
  have hpa := Finset.prod_add (fun i => sgn (x i) * sgn (y i)) (fun _ => (1 : ℝ))
      (univ : Finset (Fin n))
  simp only [Finset.prod_const_one, mul_one] at hpa
  rw [← hpa]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have h2 : ∀ i : Fin n, sgn (x i) * sgn (x i) + 1 = (2 : ℝ) := by
      intro i; rw [sgn_mul_self]; norm_num
    simp [h2]
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      exact hxy (funext fun i => not_not.mp fun hh => h ⟨i, hh⟩)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    cases hx : x i <;> cases hy : y i <;> simp [hx, hy, sgn] at hi ⊢
