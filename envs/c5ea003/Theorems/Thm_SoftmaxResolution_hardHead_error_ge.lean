-- Prove2me | Theorems.Thm_SoftmaxResolution_hardHead_error_ge
-- name    : SoftmaxResolution.hardHead_error_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:53:44.670206+00:00
-- url     : https://prove2.me/theorems/dfb2566d-b660-4db8-a949-5bd8a0bd25a0
-- title:
--   Hard selection is stuck at `1/(2N)`.
-- statement:
--   **Hard selection is stuck at `1/(2N)`.**  Whatever the selector and the stored values, a
--   hard `N`-way lookup misses the identity by at least `1/(2N)` somewhere on `[0,1]`.
--
--   Proof by pigeonhole on the `N+1` grid points `k/N`: two of them must select the same value,
--   yet they are `1/N` apart.
--
--   ```lean
--   theorem SoftmaxResolution.hardHead_error_ge{N : ℕ} (hN : 0 < N) (sel : ℝ → Fin N) (v : Fin N → ℝ) :
--       ∃ x ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) / (2 * N) ≤ |hardHead sel v x - x| := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/SoftmaxResolution.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/SoftmaxResolution.lean#L149

-- Thm stub generated from MachineLearning/TransformerUniversality/SoftmaxResolution.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_SoftmaxResolution

/-!
# Soft selection beats hard selection: refuting the `Ω(1/N)` resolution barrier for softmax heads

`Catalog/MachineLearning/TransformerUniversality/FiniteLookupSeparation.lean` proves that a
*hard* lookup architecture that reads one of `N` stored values has uniform error at least
`1/(2N)` against the identity on `[0,1]`, and that the bound is attained.  The first
next-cycle sub-conjecture of `FUTURE_DIRECTIONS.md` proposed that the same `Ω(1/N)` barrier
survives softmax: *"a softmax attention layer with `N` fixed keys and arbitrary score scale has
uniform error at least `c/N` on the identity."*

**This file refutes that conjecture.**  Softmax weights are strictly interior points of the
simplex and vary continuously with the input, so a *two*-key softmax head with values `0` and
`1` already approximates the identity on `[0,1]` to arbitrary accuracy: choosing the logit
gap `log ((x+ε)/(1+ε-x))` gives the attention weight `(x+ε)/(1+2ε)`, whose distance from `x`
is at most `ε` uniformly on `[0,1]`.  No lower bound of the form `c/N` can therefore hold.

Main results:

* `softmaxHead_le_of_le`, `le_softmaxHead_of_le` — a softmax head always outputs a point of
  the convex hull of its values (the only thing hard and soft selection have in common);
* `logitHead_eq` — the closed form `(x+ε)/(1+2ε)` of the two-key head used below;
* `two_key_softmax_approx_identity` — **`ε`-approximation of the identity on `[0,1]` with two
  keys**, for every `ε > 0`;
* `no_universal_softmax_resolution_bound` — the formal refutation: there is no constant
  `c > 0` with `c/N` uniform error for all `N`-key softmax heads;
* `hardHead_error_ge` — the contrasting hard-selection bound `1/(2N)`, proved here by
  pigeonhole on the `N+1` grid points `k/N` so that the dichotomy is self-contained;
* `soft_hard_dichotomy` — the two statements side by side at `N = 2`: error `≤ ε` for every
  `ε > 0` on the soft side, error `≥ 1/4` unconditionally on the hard side.

The moral for the scope qualification of the original development is that the `Θ(1/N)`
resolution barrier proved in `FiniteLookupSeparation.lean` is an artifact of **hard**
selection — of reading a finite value table — and not of the number of heads or keys.  A
genuine lower bound for softmax models must therefore constrain the score family (e.g. to
bilinear scores), not merely count keys.
-/

open scoped BigOperators

open SoftmaxResolution


variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem SoftmaxResolution.hardHead_error_ge{N : ℕ} (hN : 0 < N) (sel : ℝ → Fin N) (v : Fin N → ℝ) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) / (2 * N) ≤ |hardHead sel v x - x| := by sorry
