-- Prove2me | solution 1 for AlmostLossless.exact_collisionProb_planar
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:07:10.065718+00:00
-- url     : https://prove2.me/submissions/81409090-3492-4344-8697-29a22fb96603

-- Sol generated from Logic/AlmostLossless/ExactPlanar.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_ExactPlanar
import Definitions.Def_Logic_AlmostLossless_Hashing
import Theorems.Thm_AlmostLossless_exact_card_collides_planar

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
theorem solution(T : Finset (Fin 2 → ZMod p))
    (D : Finset (Fin 2 → ZMod p)) (hD : D.Nonempty) (h0 : ∀ z ∈ D, z ≠ 0)
    (hnp : ∀ z ∈ D, ∀ w ∈ D, z ≠ w → z 0 * w 1 - z 1 * w 0 ≠ 0)
    (hcov : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∃ z ∈ D, ∃ c : ZMod p, c ≠ 0 ∧ x - y = c • z)
    (hreal : ∀ z ∈ D, ∃ x ∈ T, ∃ y ∈ T, ∃ c : ZMod p, c ≠ 0 ∧ x - y = c • z) :
    (#{a : Fin 2 → ZMod p | CollidesOn (dotHash p 2) T a} : ℚ)
        / (Fintype.card (Fin 2 → ZMod p) : ℚ)
      = (1 + (D.card : ℚ) * ((p : ℚ) - 1)) / (p : ℚ) ^ 2 := by
  have hppos : 0 < p := (Fact.out (p := p.Prime)).pos
  have hcount := exact_card_collides_planar T D hD h0 hnp hcov hreal
  have hcard : Fintype.card (Fin 2 → ZMod p) = p ^ 2 := by
    simp [ZMod.card, pow_two]
  rw [hcount, hcard]
  have : ((1 + D.card * (p - 1) : ℕ) : ℚ) = 1 + (D.card : ℚ) * ((p : ℚ) - 1) := by
    push_cast [Nat.cast_sub hppos]
    ring
  rw [this]
  push_cast
  ring
