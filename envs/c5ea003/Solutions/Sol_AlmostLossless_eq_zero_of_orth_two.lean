-- Prove2me | solution 1 for AlmostLossless.eq_zero_of_orth_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:28:57.926392+00:00
-- url     : https://prove2.me/submissions/9f38d9fe-68c9-486d-8baf-5d545ce52781

-- Sol generated from Logic/AlmostLossless/ExactPlanar.lean
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


/-! ## Exact failure probability of the planar compressor -/




/-! ## A worked example, cross-checked by exhaustive computation

The hypotheses of `exact_card_collides_planar` are satisfiable: here is a
concrete typical set over `ZMod 11`.  The count predicted by the theorem
(`1 + 3·(11-1) = 31` bad seeds out of `121`) is confirmed independently by
brute-force evaluation, which also shows the theorem is not vacuous. -/










open AlmostLossless in
theorem solution{z w : Fin 2 → ZMod p} (h : z 0 * w 1 - z 1 * w 0 ≠ 0)
    {a : Fin 2 → ZMod p} (hz : dotHom z a = 0) (hw : dotHom w a = 0) : a = 0 := by
  have hz' : a 0 * z 0 + a 1 * z 1 = 0 := by
    simpa [dotHom, Fin.sum_univ_two] using hz
  have hw' : a 0 * w 0 + a 1 * w 1 = 0 := by
    simpa [dotHom, Fin.sum_univ_two] using hw
  have h0 : a 0 * (z 0 * w 1 - z 1 * w 0) = 0 := by
    linear_combination w 1 * hz' - z 1 * hw'
  have h1 : a 1 * (z 0 * w 1 - z 1 * w 0) = 0 := by
    linear_combination z 0 * hw' - w 0 * hz'
  have ha0 : a 0 = 0 := by
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact h'
    · exact absurd h' h
  have ha1 : a 1 = 0 := by
    rcases mul_eq_zero.1 h1 with h' | h'
    · exact h'
    · exact absurd h' h
  funext i
  fin_cases i
  · simpa using ha0
  · simpa using ha1
