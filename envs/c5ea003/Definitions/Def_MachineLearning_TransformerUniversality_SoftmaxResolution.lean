-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_SoftmaxResolution
-- name    : MachineLearning_TransformerUniversality_SoftmaxResolution
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:51.246503+00:00
-- url     : https://prove2.me/theorems/99abdc9f-9833-432f-94d6-b990fd3b5c2e
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_SoftmaxResolution
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.SoftmaxResolution`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/SoftmaxResolution.lean by skeleton subtraction
import Mathlib

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

namespace SoftmaxResolution

section General

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Softmax weights of a score vector (any inverse temperature is absorbed into `s`). -/
noncomputable def weight (s : ι → ℝ) (j : ι) : ℝ := Real.exp (s j) / ∑ k, Real.exp (s k)




/-- A softmax attention head with input-dependent scores `s` and fixed values `v`. -/
noncomputable def softmaxHead (s : ℝ → ι → ℝ) (v : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ j, weight (s x) j * v j



end General

section TwoKey

/-- The two-key score family used to approximate the identity: key `0` has logit `0`, key `1`
has logit `log ((x+ε)/(1+ε-x))`. -/
noncomputable def logitScore (eps : ℝ) (x : ℝ) (j : Fin 2) : ℝ :=
  if j = 0 then 0 else Real.log ((x + eps) / (1 + eps - x))

/-- The two values: `0` on key `0` and `1` on key `1`. -/
def unitValues (j : Fin 2) : ℝ := if j = 0 then 0 else 1





end TwoKey

section Hard

/-- A hard-selection head: pick one of `N` stored values by an arbitrary selector. -/
def hardHead {N : ℕ} (sel : ℝ → Fin N) (v : Fin N → ℝ) (x : ℝ) : ℝ := v (sel x)



end Hard

end SoftmaxResolution


