-- Prove2me | Theorems.Thm_AsaiSecondMoment_asai_second_moment_k_aspect
-- name    : AsaiSecondMoment.asai_second_moment_k_aspect
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:01:53.434004+00:00
-- url     : https://prove2.me/theorems/7b46792d-80ab-4000-8fbd-a2975cd09149
-- title:
--   Flagship theorem: the second moment of the convoluted central values in the `k`-aspect.
-- statement:
--   **Flagship theorem: the second moment of the convoluted central values in the `k`-aspect.**
--
--   `lam f n` are the Hecke eigenvalues of the Asai lift `As(f)`, `mu n` those of the fixed
--   Hecke–Maass form `φ`, so `lam f n * mu n` are the Rankin–Selberg coefficients of
--   `As(f) × φ`.  Given
--
--   Petersson quasi-orthogonality of the Asai eigenvalues with diagonal `D ≤ c₁ k` and
--     off-diagonal error `e` satisfying `eN ≤ c₂ k`;
--   the Hecke bound `|mu n| ≤ ν` for `φ`;
--   an approximate functional equation with `J ≥ 1` blocks of length `N ≥ 1`, archimedean
--     weights `≤ 1` and coefficient mass `≤ B`,
--
--   the second moment of the central values obeys
--
--   `∑_f |L f|² ≤ (c₁ + c₂) · ν² · J² · B · k`.
--
--   No positivity is assumed on `D`, `e`, `B` or `k`; all of it is derived.
--
--   ```lean
--   theorem AsaiSecondMoment.asai_second_moment_k_aspect(S : Finset ι) (lam : ι → ℕ → ℂ) (mu : ℕ → ℂ)
--       (N J : ℕ) (hN : 1 ≤ N) (hJ : 1 ≤ J) (D e nu k c₁ c₂ B : ℝ)
--       (hQO : QuasiOrthogonal S lam N D e) (hD : D ≤ c₁ * k) (heN : e * N ≤ c₂ * k)
--       (hnu0 : 0 ≤ nu) (hmu : ∀ n ∈ Finset.range N, ‖mu n‖ ≤ nu)
--       (w : ℕ → ℂ) (A : ℕ → ℕ → ℂ) (L : ι → ℂ)
--       (hL : AFE S (fun f n => lam f n * mu n) N J w A L)
--       (hw : ∀ j ∈ Finset.range J, ‖w j‖ ≤ 1)
--       (hB : ∀ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 ≤ B) :
--       ∑ f ∈ S, ‖L f‖ ^ 2 ≤ (c₁ + c₂) * nu ^ 2 * (J : ℝ) ^ 2 * B * k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AsaiSecondMoment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AsaiSecondMoment.lean#L150

-- Thm stub generated from Novelty/AsaiSecondMoment.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiSecondMoment
/-
# The second moment of `L(1/2, As(f) × φ)` from the large sieve

This file completes the analytic skeleton begun in `Novelty.AsaiLargeSieve`.  There we proved
that a Petersson-type quasi-orthogonality relation for the Hecke eigenvalues of the Asai
lifts `As(f)` (with `f` in a Hecke orthonormal basis of Hilbert modular cusp forms of parallel
weight `(k,k)` over a real quadratic field `F = Q(√D)`) produces a large sieve inequality,
that the constant is self-dual, and that twisting by the bounded Hecke eigenvalues of a fixed
Hecke–Maass form `φ` over `Q` costs only `ν²`.

Here we feed an **approximate functional equation** into that machine.  An AFE writes each
central value as a *short* linear combination of Dirichlet polynomials in the Rankin–Selberg
coefficients `λ_{As(f)}(n) λ_φ(n)`:

`L(1/2, As(f) × φ) = ∑_{j < J} w j · ∑_{n < N} A j n · λ_{As(f)}(n) λ_φ(n)`

(the index `j` runs over the `O(log)` dyadic blocks and the two terms of the functional
equation; `w j` are the archimedean weights and `A j n` the smoothed coefficients).

Main results:

* `AsaiSecondMoment.secondMoment_le` — the second moment of any family of values admitting
  such a decomposition is bounded by `J · ∑_j |w j|² · C · ‖A j‖²`, where `C` is *any*
  admissible large sieve constant.
* `AsaiSecondMoment.secondMoment_uniform` — the uniform form `J² · C · B`.
* `AsaiSecondMoment.asai_second_moment_k_aspect` — **the flagship statement**: from
  quasi-orthogonality with diagonal `D ≤ c₁·k` and off-diagonal error `e` with `eN ≤ c₂·k`,
  from a `ν`-bounded twisting system `mu` (the Hecke eigenvalues of `φ`) and from an AFE with
  `J` blocks and coefficient mass `≤ B`, one gets

  `∑_f |L f|² ≤ (c₁ + c₂) · ν² · J² · B · k`,

  i.e. a second moment bound that is **linear in the weight `k`** up to the `J² = O(log²k)`
  loss of the AFE — the shape of the paper's main application.
* `AsaiSecondMoment.secondMoment_saving` — the adversarial check: the same second moment,
  bounded through the *trivial* (Cauchy–Schwarz, no cancellation) large sieve constant, is
  worse by a factor `≍ N`; so the bound above is genuinely non-trivial exactly in the regime
  `eN ≤ D` where the Kloosterman/Salié term is under control.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the passage AFE → second moment should cost exactly the square of
the number of blocks and nothing else; in particular the `k`-aspect exponent of the second
moment should be *inherited verbatim* from the diagonal `D` of the Petersson formula, with
the length `N` of the AFE entering only through the product `eN`.  Bold form: no analytic
input beyond `‖∑_{j<J} x_j‖² ≤ J ∑ ‖x_j‖²` is needed.

Experiment (Experimenter): confirmed.  `secondMoment_le` needs only the squared triangle
inequality plus the large sieve applied to each block after absorbing the weight `w j` into
the coefficients (`linForm` is linear in the coefficient vector, which is why the constant
`C` may be used blockwise with no loss).  The `k`-aspect corollary then composes
`largeSieve_of_quasiOrthogonal`, `largeSieve_twist` and `secondMoment_uniform`; positivity of
the large sieve constant is *not* assumed but derived from `diagonal_le_of_largeSieve`.

Analysis (Analyst): a first attempt assumed `0 ≤ D`, `0 ≤ e`, `0 ≤ B`, `0 ≤ k` as separate
hypotheses.  All four are removable: `e ≥ 0` follows from quasi-orthogonality on a nonempty
range, `D + eN ≥ 0` from the diagonal test vector, `B ≥ 0` from a nonempty block set, and the
`k`-positivity is never needed because only the product `(c₁+c₂)k` is compared with the
nonnegative quantity `D + eN`.  Removing them is what makes the final statement faithful:
no hidden assumption can make it vacuous.

Critique (Critic): could the flagship theorem be vacuous, e.g. by unsatisfiable hypotheses?
No: `AsaiSecondMoment.exists_nontrivial_instance` exhibits a concrete nonzero instance of the
full hypothesis package (an orthonormal system with `D = 1`, `e = 0`), in which the conclusion
is a genuine nonzero inequality.  Could it be weak?  `secondMoment_saving` measures precisely
the factor `N` that separates it from the trivial bound.
-/

open Finset Complex AsaiLargeSieve

open AsaiSecondMoment

variable {ι : Type*}

theorem AsaiSecondMoment.asai_second_moment_k_aspect(S : Finset ι) (lam : ι → ℕ → ℂ) (mu : ℕ → ℂ)
    (N J : ℕ) (hN : 1 ≤ N) (hJ : 1 ≤ J) (D e nu k c₁ c₂ B : ℝ)
    (hQO : QuasiOrthogonal S lam N D e) (hD : D ≤ c₁ * k) (heN : e * N ≤ c₂ * k)
    (hnu0 : 0 ≤ nu) (hmu : ∀ n ∈ Finset.range N, ‖mu n‖ ≤ nu)
    (w : ℕ → ℂ) (A : ℕ → ℕ → ℂ) (L : ι → ℂ)
    (hL : AFE S (fun f n => lam f n * mu n) N J w A L)
    (hw : ∀ j ∈ Finset.range J, ‖w j‖ ≤ 1)
    (hB : ∀ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 ≤ B) :
    ∑ f ∈ S, ‖L f‖ ^ 2 ≤ (c₁ + c₂) * nu ^ 2 * (J : ℝ) ^ 2 * B * k := by sorry
