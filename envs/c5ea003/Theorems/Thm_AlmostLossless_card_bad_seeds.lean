-- Prove2me | Theorems.Thm_AlmostLossless_card_bad_seeds
-- name    : AlmostLossless.card_bad_seeds
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:15:59.738481+00:00
-- url     : https://prove2.me/theorems/fa091942-8733-4bd9-b745-faa77bf5a724
-- title:
--   Exact count of bad seeds.
-- statement:
--   **Exact count of bad seeds.**  If `D` is a nonempty set of pairwise
--   non-proportional nonzero directions, the seeds orthogonal to at least one of
--   them form a pencil of `|D|` lines through the origin, of total size
--   `1 + |D|(p-1)`.
--
--   ```lean
--   theorem AlmostLossless.card_bad_seeds(D : Finset (Fin 2 → ZMod p)) (hD : D.Nonempty)
--       (h0 : ∀ z ∈ D, z ≠ 0)
--       (hnp : ∀ z ∈ D, ∀ w ∈ D, z ≠ w → z 0 * w 1 - z 1 * w 0 ≠ 0) :
--       #{a : Fin 2 → ZMod p | ∃ z ∈ D, dotHom z a = 0} = 1 + D.card * (p - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/ExactPlanar.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/ExactPlanar.lean#L91

-- Thm stub generated from Logic/AlmostLossless/ExactPlanar.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_ExactPlanar
import Definitions.Def_Logic_AlmostLossless_Hashing

/-!
# The exact failure probability of the planar inner-product compressor

The union bound of `AlmostLossless.collisionProb_le` charges one `1/p` per pair
of typical words.  In dimension `k = 2` the truth is *exactly* computable, and
it is strictly better whenever two pairs of typical words happen to differ by
proportional vectors: only the **projective directions** of the difference set
matter.

For a seed `a ∈ (ZMod p)²` the hash `x ↦ ⟨a,x⟩` confuses `x` and `y` iff `a`
lies on the line orthogonal to `x - y`.  Distinct projective directions give
lines meeting only at the origin, so the bad seeds form a "pencil" of `d` lines
through `0`:

`#{bad seeds} = 1 + d·(p-1)`, i.e. `P(failure) = (1 + d(p-1))/p²`,

where `d` is the number of distinct directions among the differences of typical
words (`AlmostLossless.exact_card_collides_planar`).  Since `d ≤ |T|(|T|-1)/2`,
this refines the union bound, and it is an *equality*, so the falsifiability
gate of the research thread is met with an exact figure rather than a bound.

This is a small bridge between finite projective geometry over `𝔽_p` and the
Monte-Carlo analysis of a compressor.
-/

open AlmostLossless

open Finset


variable {p : ℕ} [Fact p.Prime]

/-! ## Elementary identities for the inner-product hash -/







/-! ## The pencil of bad seeds -/

theorem AlmostLossless.card_bad_seeds(D : Finset (Fin 2 → ZMod p)) (hD : D.Nonempty)
    (h0 : ∀ z ∈ D, z ≠ 0)
    (hnp : ∀ z ∈ D, ∀ w ∈ D, z ≠ w → z 0 * w 1 - z 1 * w 0 ≠ 0) :
    #{a : Fin 2 → ZMod p | ∃ z ∈ D, dotHom z a = 0} = 1 + D.card * (p - 1) := by sorry
