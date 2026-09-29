-- Prove2me | Theorems.Thm_ErdosProblems_Shared_IdealCounting_sum_countSupp_mul_le
-- name    : ErdosProblems.Shared.IdealCounting.sum_countSupp_mul_le
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:54:21.238127+00:00
-- url     : https://prove2.me/theorems/a5a5827f-4873-471d-97e7-24e430f91326
-- title:
--   Lean source theorem: sum_countSupp_mul_le
-- statement:
--   If every prime ideal satisfying P has two distinct prime ideals above it in M, each with the same norm, then for nonzero n the divisor-pair convolution of the P-supported ideal counts is bounded by the number of ideals of norm n in M.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Shared/IdealCountingEuler.lean#L152-L304
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Mathlib.Analysis.PSeries
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int

/-!
# Counting ideals by their prime factors in a number field

For a number field `K` and a predicate `P` on ideals of `𝓞 K`, `countSupp K P n` is the
number of ideals of absolute norm `n` all of whose prime factors satisfy `P`.  This file
proves the three coefficientwise facts that feed the pole comparison of
`ErdosProblems.Shared.DirichletPole`:

* `card_le_sum_countSupp` (**factorisation into two parts**): every ideal of norm `n` is the
  product of its `P`-part and its `¬P`-part, so the number of ideals of norm `n` is at most the
  Dirichlet convolution of the two restricted counts;
* `sum_countSupp_div_le` (**the bad part converges at `s = 1`**): when `P 𝔭` says that the
  norm of `𝔭` is a prime larger than `N₀`, the series `∑ countSupp K (¬P) n / n` has bounded
  partial sums.  The primes excluded are finitely many primes of small norm and primes of
  norm `p ^ f` with `f ≥ 2`; at most `[K : ℚ]` primes lie over each `p`, so their
  reciprocal norms are dominated by `[K : ℚ] ∑ 1 / p²`, and a finite Euler product over the
  primes involved bounds the whole series;
* `sum_countSupp_mul_le` (**split primes double the count**): if every prime `𝔭` with `P 𝔭`
  has two distinct primes of an extension `M` above it, each of the same norm as `𝔭`, then
  the Dirichlet convolution of the `P`-count with itself is at most the number of ideals of
  `𝓞 M` of norm `n`.  The injection sends a pair of ideals `(I, J)` to the product of the
  first lifts of the prime factors of `I` and the second lifts of those of `J`.
-/

noncomputable section


open NumberField UniqueFactorizationMonoid Ideal

variable (K : Type*) [Field K] [NumberField K]





variable {K}











/-! ### Factorisation into a `P`-part and a `¬P`-part -/







/-! ### Split primes: the convolution of the `P`-count with itself -/

open ErdosProblems.Shared.IdealCounting

theorem ErdosProblems.Shared.IdealCounting.sum_countSupp_mul_le (M : Type*) [Field M] [NumberField M] [Algebra K M]
    (P : Ideal (𝓞 K) → Prop)
    (hsplit : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → P 𝔭 →
      ∃ Q₁ Q₂ : Ideal (𝓞 M), Q₁.IsPrime ∧ Q₁ ≠ ⊥ ∧ Q₂.IsPrime ∧ Q₂ ≠ ⊥ ∧
        absNorm Q₁ = absNorm 𝔭 ∧ absNorm Q₂ = absNorm 𝔭 ∧
        Q₁.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧ Q₂.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧
        Q₁ ≠ Q₂)
    {n : ℕ} (hn : n ≠ 0) :
    ∑ x ∈ n.divisorsAntidiagonal, countSupp K P x.1 * countSupp K P x.2 ≤
      Nat.card {Q : Ideal (𝓞 M) // absNorm Q = n} := by sorry
