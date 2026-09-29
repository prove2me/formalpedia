-- Prove2me | Theorems.Thm_LowRankQuantitative_exists_entry_far_from_smul_one
-- name    : LowRankQuantitative.exists_entry_far_from_smul_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:42:30.237334+00:00
-- url     : https://prove2.me/theorems/ba8ef4b0-a4aa-4427-b036-b0f9395a758d
-- title:
--   Quantitative rank obstruction.
-- statement:
--   **Quantitative rank obstruction.**  A matrix of rank `< n` is entrywise at distance at
--   least `β / n` from `β` times the identity.
--
--   The bound is genuinely quantitative: the classical statement "a singular matrix is not `β • 1`"
--   is the special case `β / n > 0`, but here the distance is bounded below by an explicit constant
--   depending only on the dimension and the score scale.
--
--   ```lean
--   theorem LowRankQuantitative.exists_entry_far_from_smul_one(hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
--       (hrank : S.rank < n) {beta : ℝ} (hbeta : 0 ≤ beta) :
--       ∃ i j, beta / n ≤ |S i j - beta * (1 : Matrix (Fin n) (Fin n) ℝ) i j| := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/LowRankQuantitative.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/LowRankQuantitative.lean#L50

-- Thm stub generated from MachineLearning/TransformerUniversality/LowRankQuantitative.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_LowRankQuantitative

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

open LowRankQuantitative


variable {n : ℕ}

theorem LowRankQuantitative.exists_entry_far_from_smul_one(hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hrank : S.rank < n) {beta : ℝ} (hbeta : 0 ≤ beta) :
    ∃ i j, beta / n ≤ |S i j - beta * (1 : Matrix (Fin n) (Fin n) ℝ) i j| := by sorry
