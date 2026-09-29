-- Prove2me | Theorems.Thm_AlmostLossless_card_sum_le_card_biUnion_add_offDiag
-- name    : AlmostLossless.card_sum_le_card_biUnion_add_offDiag
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:42.658006+00:00
-- url     : https://prove2.me/theorems/efa1ce75-7e8e-4d4d-9bb4-73e37898aa52
-- title:
--   Second Bonferroni inequality, counting form:
-- statement:
--   **Second Bonferroni inequality**, counting form:
--   `∑ |A i| ≤ |⋃ A i| + ∑_{i ≠ j} |A i ∩ A j|` (ordered pairs).
--   Proved by induction on the index set.
--
--   ```lean
--   theorem AlmostLossless.card_sum_le_card_biUnion_add_offDiag{ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
--       (A : ι → Finset Ω) (I : Finset ι) :
--       ∑ i ∈ I, (A i).card ≤ (I.biUnion A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessConverse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessConverse.lean#L72

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

theorem AlmostLossless.card_sum_le_card_biUnion_add_offDiag{ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (A : ι → Finset Ω) (I : Finset ι) :
    ∑ i ∈ I, (A i).card ≤ (I.biUnion A).card + ∑ p ∈ I.offDiag, (A p.1 ∩ A p.2).card := by sorry
