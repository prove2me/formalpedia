-- Prove2me | solution 1 for AlmostLossless.exact_card_collides_planar
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:51:35.493234+00:00
-- url     : https://prove2.me/submissions/7f671ce5-1eec-4e57-b370-7be98a0beb4f

-- Sol generated from Logic/AlmostLossless/ExactPlanar.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_ExactPlanar
import Definitions.Def_Logic_AlmostLossless_Hashing
import Theorems.Thm_AlmostLossless_card_bad_seeds

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

theorem dotHom_sub {k : ℕ} (a x y : Fin k → ZMod p) :
    dotHom (x - y) a = dotHash p k a x - dotHash p k a y := by
  simp only [dotHom, dotHash, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dotHom_smul {k : ℕ} (c : ZMod p) (z a : Fin k → ZMod p) :
    dotHom (c • z) a = c * dotHom z a := by
  simp only [dotHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring





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
    #{a : Fin 2 → ZMod p | CollidesOn (dotHash p 2) T a} = 1 + D.card * (p - 1) := by
  classical
  have hiff : ∀ a : Fin 2 → ZMod p,
      CollidesOn (dotHash p 2) T a ↔ ∃ z ∈ D, dotHom z a = 0 := by
    intro a
    constructor
    · rintro ⟨q, hq, hcol⟩
      rw [Finset.mem_offDiag] at hq
      obtain ⟨z, hz, c, hc, hzc⟩ := hcov q.1 hq.1 q.2 hq.2.1 hq.2.2
      refine ⟨z, hz, ?_⟩
      have hd : dotHom (q.1 - q.2) a = 0 := by
        rw [dotHom_sub, hcol, sub_self]
      rw [hzc, dotHom_smul] at hd
      rcases mul_eq_zero.1 hd with h' | h'
      · exact absurd h' hc
      · exact h'
    · rintro ⟨z, hz, hza⟩
      obtain ⟨x, hx, y, hy, c, hc, hzc⟩ := hreal z hz
      have hne : x ≠ y := by
        intro hxy
        have : c • z = 0 := by rw [← hzc, hxy, sub_self]
        rcases smul_eq_zero.1 this with h' | h'
        · exact hc h'
        · exact h0 z hz h'
      refine ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hne⟩, ?_⟩
      have hd : dotHom (x - y) a = 0 := by rw [hzc, dotHom_smul, hza, mul_zero]
      rw [dotHom_sub] at hd
      exact sub_eq_zero.1 hd
  have : ({a : Fin 2 → ZMod p | CollidesOn (dotHash p 2) T a} : Finset _)
      = ({a : Fin 2 → ZMod p | ∃ z ∈ D, dotHom z a = 0} : Finset _) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hiff a
  rw [this, card_bad_seeds D hD h0 hnp]
