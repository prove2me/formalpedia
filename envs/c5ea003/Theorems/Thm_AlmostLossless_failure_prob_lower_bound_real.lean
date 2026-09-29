-- Prove2me | Theorems.Thm_AlmostLossless_failure_prob_lower_bound_real
-- name    : AlmostLossless.failure_prob_lower_bound_real
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:57.17769+00:00
-- url     : https://prove2.me/theorems/a5988899-2648-4b32-b57c-f7b951d0b979
-- title:
--   Random hashing really does pay the `1/ε` factor.
-- statement:
--   **Random hashing really does pay the `1/ε` factor.**  If the typical set is
--   not too large compared with the codebook (`2(k-1) ≤ M`, where `k = |S| - 1`), then
--   the failure probability of a uniformly random codebook is at least `k / (2M)`.
--   Consequently `P[failure] ≤ ε` forces `M ≥ k/(2ε)`, whereas the converse bound
--   `converse_rate` only demands `M ≥ (1-ε)|S|`: the `Θ(1/ε)` overhead is intrinsic to
--   the random codebook, not to the union-bound analysis.
--
--   ```lean
--   theorem AlmostLossless.failure_prob_lower_bound_real(S : Finset α) (x : α) (hM : 0 < M)
--       (hk : 2 * ((S.erase x).card - 1) ≤ M) :
--       ((S.erase x).card : ℝ) / (2 * M)
--         ≤ ((failSet S x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessConverse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessConverse.lean#L240

-- Thm stub generated from Geometry/AlmostLosslessConverse.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
/-
# How far beyond the pigeonhole bound can one go?  Converse and tightness

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

Two adversarial questions about the almost-lossless scheme of
`Geometry.AlmostLosslessDecoder`:

1. *How much can the counting bound really be relaxed?*
   `AlmostLossless.converse_card_good_le` — **the ε-relaxed pigeonhole bound**:
   for **any** encoder/decoder pair whatsoever, the set of strings decoded
   correctly has size at most `M`.  So a `(1-ε)`-reliable code for a typical set
   `S` still needs `M ≥ (1-ε)|S|`: relaxation buys a factor `(1-ε)`, no more.

2. *Is the `1/ε` overhead of random hashing an artefact of the union bound?*
   No.  `AlmostLossless.failure_prob_lower_bound` is a **Bonferroni lower bound**
   on the failure probability of uniform random hashing:
   `P[failure] ≥ (|S|-1) / (2M)` once `2(|S|-2) ≤ M`.
   Hence uniform random hashing genuinely needs `M ≳ |S| / ε`, a factor `Θ(1/ε)`
   above the converse — the gap is a property of the *random codebook*, not of
   the analysis.

Supporting combinatorics proved here from scratch:
* `AlmostLossless.card_sum_le_card_biUnion_add_offDiag` — the second Bonferroni
  inequality for an arbitrary finite family of finite sets.
* `AlmostLossless.card_doubleCollision_mul_le` — a two-coordinate refinement of
  the marginal count of `AlmostLosslessCore`: two prescribed collisions have
  probability `1/M²`.
-/

open AlmostLossless

open Finset

/-! ## 1. The ε-relaxed pigeonhole bound (converse) -/



/-! ## 2. Bonferroni: a lower bound for unions of finite sets -/


/-! ## 3. Two prescribed collisions have probability `1/M²` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}


/-! ## 4. The failure probability of random hashing is genuinely `≍ |S|/M` -/

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem AlmostLossless.failure_prob_lower_bound_real(S : Finset α) (x : α) (hM : 0 < M)
    (hk : 2 * ((S.erase x).card - 1) ≤ M) :
    ((S.erase x).card : ℝ) / (2 * M)
      ≤ ((failSet S x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α) := by sorry
