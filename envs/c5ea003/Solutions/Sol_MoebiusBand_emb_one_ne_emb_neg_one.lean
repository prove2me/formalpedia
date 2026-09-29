-- Prove2me | solution 1 for MoebiusBand.emb_one_ne_emb_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:26:11.018496+00:00
-- url     : https://prove2.me/submissions/6a27d44e-0689-4185-af10-46240c822eea

-- Sol generated from MachineLearning/MoebiusBandArithmetic.lean
import Mathlib
import Definitions.Def_MachineLearning_MoebiusBandArithmetic
import Theorems.Thm_MoebiusBand_emb_eq_iff
import Theorems.Thm_MoebiusBand_emb_fst_eq_zero_iff

/-!
# Arithmetic on the Möbius band: testing the "Möbius integers" conjecture

The Möbius band is modelled as `M = ([0,1] × ℝ)/((0,y) ∼ (1,−y))`, realised here as
the quotient of `ℝ × ℝ` by the relation `MoebRel` that identifies `(0,y)` with
`(1,−y)` (points outside the seam are identified with nothing but themselves).

The proposed "Möbius integers" are the images of

  `emb n = (1/2 + 1/(2n), |n|)`.

We test every claim of the conjecture. The outcome is a mixture of one confirmation
and four refutations:

* **Confirmed.** The value map `val (x,y) = y(2x−1)` *is* well defined on `M`
  (`val_respects`, `valM`), and the seam point is genuinely twisted:
  `⟦(0,−1)⟧ = ⟦(1,1)⟧` (`twist_point`).
* **Refuted (no induced ring).** Neither coordinatewise addition nor coordinatewise
  multiplication descends to `M`: `no_induced_add`, `no_induced_mul`. Hence
  "`Z_M` is a ring under the induced operations from `ℝ × ℝ/∼`" is false at the
  level of the operations themselves.
* **Refuted (the value map collapses ℤ).** `val (emb n) = sign n`
  (`val_emb`), so the embedding does *not* represent `n`; it only records its sign,
  and e.g. `2` and `3` receive the same value (`val_collapse`).
* **Refuted (1 and −1 are not identified).** `⟦emb 1⟧ ≠ ⟦emb (−1)⟧`
  (`emb_one_ne_emb_neg_one`); in fact `emb` is injective into `M`
  (`emb_injective`), so `Z_M ≃ ℤ` as a set — no one-point compactification.
  Moreover `Z_M` is unbounded, hence not compact (`emb_range_not_compact`).
* **Refuted (the proposed zero divisors).** The alleged nonzero factor `(1,0)` is
  *equal to zero* in `M` (`one_zero_eq_zero`) and is not a Möbius integer at all
  (`one_zero_not_moebius_integer`).

The positive algebraic content that survives is developed in
`MachineLearning.MoebiusTwistRing`, where the twist is a unit of order two in
`ℤ[t]/(t²−1)`, a genuine commutative ring that is not a domain.
-/

open MoebiusBand








theorem pt_eq_iff {p q : ℝ × ℝ} : pt p = pt q ↔ MoebRel p q :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-! ### Confirmed: the value map descends -/






/-! ### Refuted: no induced ring operations -/



/-! ### The proposed embedding of ℤ -/











/-! ### Refuted: the proposed zero divisors -/





open MoebiusBand in
theorem solution: pt (emb 1) ≠ pt (emb (-1)) := by
  rw [Ne, pt_eq_iff]
  intro h
  rcases h with h | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have := emb_eq_iff.mp h
    norm_num at this
  · rw [emb_fst_eq_zero_iff] at h0
    norm_num at h0
  · -- here `emb 1 = (1, 1)` and `emb (-1) = (0, 1)`, so the seam would force `1 = −1`
    have hone : |((1 : ℤ) : ℝ)| = 1 := by norm_num
    have hneg : |(((-1 : ℤ)) : ℝ)| = 1 := by norm_num
    simp only [emb] at h2
    rw [hone, hneg] at h2
    norm_num at h2
