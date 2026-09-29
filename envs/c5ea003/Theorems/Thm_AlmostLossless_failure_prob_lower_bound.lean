-- Prove2me | Theorems.Thm_AlmostLossless_failure_prob_lower_bound
-- name    : AlmostLossless.failure_prob_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:04:40.01336+00:00
-- url     : https://prove2.me/theorems/60dd351a-9556-459e-9029-0e6345527e6a
-- title:
--   **Bonferroni lower bound on the failure probability of uniform random
-- statement:
--   **Bonferroni lower bound on the failure probability of uniform random
--   hashing** (counting form).  With `k = |S| - 1` competitors and `N = M^{|α|}`
--   codebooks:
--   `k · M · N ≤ M² · |failSet| + k(k-1) · N`.
--   Together with the trivial upper bound this pins the failure probability of the
--   random codebook at `Θ(k/M)` in the regime `k ≲ M`.
--
--   ```lean
--   theorem AlmostLossless.failure_prob_lower_bound(S : Finset α) (x : α) :
--       (S.erase x).card * M * M ^ Fintype.card α
--         ≤ M ^ 2 * (failSet S x M).card
--           + (S.erase x).offDiag.card * M ^ Fintype.card α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessConverse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessConverse.lean#L196

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

theorem AlmostLossless.failure_prob_lower_bound(S : Finset α) (x : α) :
    (S.erase x).card * M * M ^ Fintype.card α
      ≤ M ^ 2 * (failSet S x M).card
        + (S.erase x).offDiag.card * M ^ Fintype.card α := by sorry
