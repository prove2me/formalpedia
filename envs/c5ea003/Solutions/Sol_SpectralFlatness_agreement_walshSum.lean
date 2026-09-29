-- Prove2me | solution 1 for SpectralFlatness.agreement_walshSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:33:28.013494+00:00
-- url     : https://prove2.me/submissions/c62d8d50-4ce6-4f90-990e-426fc963623c

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




theorem prod_sgn_sq (A : Finset (Fin n)) (x : Fin n → Bool) :
    (∏ i ∈ A, sgn (x i)) * (∏ i ∈ A, sgn (x i)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => sgn_mul_self (x i)

theorem walshChar_mul_self (S : Finset (Fin n)) (x : Fin n → Bool) :
    walshChar S x * walshChar S x = 1 := prod_sgn_sq S x

/-- A Walsh character takes only the values `±1`. -/
theorem walshChar_eq_one_or (S : Finset (Fin n)) (x : Fin n → Bool) :
    walshChar S x = 1 ∨ walshChar S x = -1 := by
  have h := walshChar_mul_self S x
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1






/-! ### Walsh coefficients and Parseval -/







/-! ### Correlation is prediction advantage: the 1/2 barrier -/






/-! ### Flatness: the noise floor, few heavy coefficients, spectral spreading -/





/-! ### Low-degree scans -/






open SpectralFlatness in
theorem solution{f : (Fin n → Bool) → ℝ} (hf : IsSignFn f) (S : Finset (Fin n)) :
    walshSum f S = 2 * (agree f S : ℝ) - 2 ^ n := by
  classical
  have hsplit : ∑ x : Fin n → Bool, f x * walshChar S x
      = (∑ x ∈ (univ : Finset (Fin n → Bool)).filter (fun x => f x = walshChar S x),
            f x * walshChar S x)
        + ∑ x ∈ (univ : Finset (Fin n → Bool)).filter (fun x => ¬ f x = walshChar S x),
            f x * walshChar S x :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hpos : ∀ x ∈ (univ : Finset (Fin n → Bool)).filter (fun x => f x = walshChar S x),
      f x * walshChar S x = 1 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2]
    exact walshChar_mul_self S x
  have hneg : ∀ x ∈ (univ : Finset (Fin n → Bool)).filter (fun x => ¬ f x = walshChar S x),
      f x * walshChar S x = -1 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rcases hf x with h1 | h1 <;> rcases walshChar_eq_one_or S x with h2 | h2 <;>
      simp [h1, h2] at hx ⊢
  rw [walshSum, hsplit, Finset.sum_congr rfl hpos, Finset.sum_congr rfl hneg]
  have hcard : ((univ : Finset (Fin n → Bool)).filter (fun x => f x = walshChar S x)).card
      + ((univ : Finset (Fin n → Bool)).filter (fun x => ¬ f x = walshChar S x)).card
      = 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp [Finset.card_univ]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg_one, agree]
  have : (((univ : Finset (Fin n → Bool)).filter (fun x => ¬ f x = walshChar S x)).card : ℝ)
      = 2 ^ n - (agree f S : ℝ) := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hcard
    push_cast at this
    simp only [agree]
    linarith
  rw [this]
  simp only [agree]
  ring
