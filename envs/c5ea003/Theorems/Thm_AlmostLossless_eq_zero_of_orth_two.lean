-- Prove2me | Theorems.Thm_AlmostLossless_eq_zero_of_orth_two
-- name    : AlmostLossless.eq_zero_of_orth_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:15:51.295786+00:00
-- url     : https://prove2.me/theorems/cbaef276-56bb-447f-b5d6-36e4985907d1
-- title:
--   Two non-proportional directions give lines meeting only at the origin.
-- statement:
--   Two non-proportional directions give lines meeting only at the origin.
--
--   ```lean
--   theorem AlmostLossless.eq_zero_of_orth_two{z w : Fin 2 → ZMod p} (h : z 0 * w 1 - z 1 * w 0 ≠ 0)
--       {a : Fin 2 → ZMod p} (hz : dotHom z a = 0) (hw : dotHom w a = 0) : a = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/ExactPlanar.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/ExactPlanar.lean#L65

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

theorem AlmostLossless.eq_zero_of_orth_two{z w : Fin 2 → ZMod p} (h : z 0 * w 1 - z 1 * w 0 ≠ 0)
    {a : Fin 2 → ZMod p} (hz : dotHom z a = 0) (hw : dotHom w a = 0) : a = 0 := by sorry
