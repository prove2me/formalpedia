-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_LowRankQuantitative
-- name    : MachineLearning_TransformerUniversality_LowRankQuantitative
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:36.446485+00:00
-- url     : https://prove2.me/theorems/438e71c6-48da-40da-b180-1b5ca9f72807
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_LowRankQuantitative
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.LowRankQuantitative`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/LowRankQuantitative.lean by skeleton subtraction
import Mathlib

/-!
# A quantitative low-rank obstruction for narrow attention heads

`Catalog/MachineLearning/TransformerUniversality/MultiHeadPlumbing.lean` proves the *exact*
low-rank bottleneck for query/key projections: the learned score matrix of a head of width
`dk` is `WQᵀ * WK`, its rank is at most `dk`, and consequently for `dk < d` it can never be
*equal* to the identity score pattern (`qk_ne_one_of_headDim_lt`).

Conjecture 5 of `FUTURE_DIRECTIONS.md` asked for the quantitative version of that statement:
being merely *unequal* to the identity is no obstruction at all in an approximation theory,
since a matrix can be unequal to the identity and yet within `10^{-9}` of it entrywise.  This
file proves the quantitative form, and in the temperature-aware shape that the conjecture
needs.

Main results:

* `exists_entry_far_from_smul_one` — a purely linear-algebraic statement: if
  `S : Matrix (Fin n) (Fin n) ℝ` has rank `< n`, then for every score scale `β ≥ 0` some entry
  of `S` differs from the corresponding entry of `β • 1` by at least `β / n`.  The proof takes
  a kernel vector `v`, normalizes it in the `ℓ¹` norm, and compares the quadratic form of
  `S - β • 1` at `v` (which equals `-β‖v‖₂²`) with its entrywise bound; the gap between the
  `ℓ¹` and `ℓ²` norms — i.e. Cauchy–Schwarz — is exactly where the factor `1/n` comes from.
* `entrywise_distance_to_identity_eq` — **the constant `1/n` is sharp**: the centering matrix
  `1 - (1/n) J` is singular and uniformly `1/n`-close to the identity, so the entrywise
  distance from the identity to the singular matrices is exactly `1/n`;
* `qk_far_from_scaled_identity` — the architectural corollary: for `dk < d`, **no** query/key
  pair of head width `dk` realizes the scaled identity score pattern to entrywise accuracy
  better than `β / d`.
* `qk_no_eps_identity` — the contrapositive as an impossibility statement: an `ε`-accurate
  identity score pattern with `ε < β / d` forces `d ≤ dk`.
* `headDim_lower_bound_of_approx` — the resulting **head-width lower bound**: to implement the
  exact-selection score pattern at scale `β` within entrywise error `ε`, one needs
  `dk ≥ d` whenever `ε < β / d`.

The point of the `β` in these statements is that the obstruction is *scale invariant*: raising
the score scale (equivalently, lowering the softmax temperature) raises the achievable error
floor by exactly the same factor, so the head-width resource of `MultiHeadPlumbing.lean` and
the temperature resource of `SoftmaxLookup.lean` cannot be traded against each other.
-/

open scoped BigOperators

namespace LowRankQuantitative

section Algebra

variable {n : ℕ}



section Sharpness

variable {n : ℕ}

/-- The centering matrix `1 - (1/n) J`: the orthogonal projection onto the mean-zero
hyperplane.  It is the extremal example for the bound above. -/
noncomputable def centering (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹




end Sharpness

end Algebra

section Heads

open Matrix

variable {d dk : ℕ}

/-- The learned score matrix of a head with query projection `WQ` and key projection `WK`
(cf. `MultiHeadPlumbing.qkScore_eq_bilinear`). -/
def scoreMatrix (WQ WK : Matrix (Fin dk) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := WQᵀ * WK





end Heads

end LowRankQuantitative


