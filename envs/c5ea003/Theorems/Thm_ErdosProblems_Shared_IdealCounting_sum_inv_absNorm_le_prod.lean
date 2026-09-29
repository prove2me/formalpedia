-- Prove2me | Theorems.Thm_ErdosProblems_Shared_IdealCounting_sum_inv_absNorm_le_prod
-- name    : ErdosProblems.Shared.IdealCounting.sum_inv_absNorm_le_prod
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:54:12.397446+00:00
-- url     : https://prove2.me/theorems/dea66c53-bfd0-4f04-8e7a-f5cbfe4aed7d
-- title:
--   Lean source theorem: sum_inv_absNorm_le_prod
-- statement:
--   If a finite set F of prime ideals has norm at least two, the reciprocal-norm sum over a finite family of nonzero ideals supported on F is at most the Euler product of (1−1/norm 𝔭)⁻¹ over F.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Shared/IdealCountingEuler.lean#L308-L364
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



/-! ### A finite Euler product bound -/

open ErdosProblems.Shared.IdealCounting

theorem ErdosProblems.Shared.IdealCounting.sum_inv_absNorm_le_prod (F : Finset (Ideal (𝓞 K))) (hF : ∀ 𝔭 ∈ F, 2 ≤ absNorm 𝔭)
    (T : Finset (Ideal (𝓞 K)))
    (hT : ∀ I ∈ T, I ≠ ⊥ ∧ ∀ 𝔭 ∈ normalizedFactors I, 𝔭 ∈ F) :
    ∑ I ∈ T, ((absNorm I : ℝ))⁻¹ ≤ ∏ 𝔭 ∈ F, (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹ := by sorry
