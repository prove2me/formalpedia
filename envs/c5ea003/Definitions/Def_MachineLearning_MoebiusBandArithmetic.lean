-- Prove2me | Definitions.Def_MachineLearning_MoebiusBandArithmetic
-- name    : MachineLearning_MoebiusBandArithmetic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:35.114988+00:00
-- url     : https://prove2.me/theorems/4699eaa4-51a3-49e2-b895-5d5af50788d1
-- title:
--   Aether Catalog definitions — MachineLearning_MoebiusBandArithmetic
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.MoebiusBandArithmetic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/MoebiusBandArithmetic.lean by skeleton subtraction
import Mathlib

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

namespace MoebiusBand

/-- The seam relation of the Möbius band: `(0,y) ∼ (1,−y)`. -/
def MoebRel (p q : ℝ × ℝ) : Prop :=
  p = q ∨ (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = -p.2) ∨ (p.1 = 1 ∧ q.1 = 0 ∧ q.2 = -p.2)

theorem moebRel_refl (p : ℝ × ℝ) : MoebRel p p := Or.inl rfl

theorem moebRel_symm {p q : ℝ × ℝ} (h : MoebRel p q) : MoebRel q p := by
  rcases h with rfl | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨h1, h0, by rw [h2]; ring⟩)
  · exact Or.inr (Or.inl ⟨h1, h0, by rw [h2]; ring⟩)

theorem moebRel_trans {p q r : ℝ × ℝ} (hpq : MoebRel p q) (hqr : MoebRel q r) :
    MoebRel p r := by
  rcases hpq with rfl | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact hqr
  · rcases hqr with rfl | ⟨g0, g1, g2⟩ | ⟨g0, g1, g2⟩
    · exact Or.inr (Or.inl ⟨h0, h1, h2⟩)
    · exact absurd (h1 ▸ g0) (by norm_num)
    · left
      have hr1 : r.1 = p.1 := by rw [g1, h0]
      have hr2 : r.2 = p.2 := by rw [g2, h2]; ring
      exact Prod.ext hr1.symm hr2.symm
  · rcases hqr with rfl | ⟨g0, g1, g2⟩ | ⟨g0, g1, g2⟩
    · exact Or.inr (Or.inr ⟨h0, h1, h2⟩)
    · left
      have hr1 : r.1 = p.1 := by rw [g1, h0]
      have hr2 : r.2 = p.2 := by rw [g2, h2]; ring
      exact Prod.ext hr1.symm hr2.symm
    · exact absurd (h1 ▸ g0) (by norm_num)

instance moebSetoid : Setoid (ℝ × ℝ) where
  r := MoebRel
  iseqv := ⟨moebRel_refl, moebRel_symm, moebRel_trans⟩

/-- The Möbius band as a quotient. -/
def M : Type := Quotient moebSetoid

/-- The class of a point. -/
def pt (p : ℝ × ℝ) : M := Quotient.mk moebSetoid p


/-! ### Confirmed: the value map descends -/

/-- The proposed value of a point: `val (x,y) = y (2x − 1)`. -/
def val (p : ℝ × ℝ) : ℝ := p.2 * (2 * p.1 - 1)

/-- The value map respects the Möbius identification — this part of the conjecture
is correct, and it is exactly the statement that `val` is a section of the twisted
line bundle. -/
theorem val_respects {p q : ℝ × ℝ} (h : MoebRel p q) : val p = val q := by
  rcases h with rfl | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · rfl
  · simp [val, h0, h1, h2]; ring
  · simp [val, h0, h1, h2]; ring

/-- The induced value map on the Möbius band. -/
def valM : M → ℝ := Quotient.lift val fun _ _ h => val_respects h



/-! ### Refuted: no induced ring operations -/



/-! ### The proposed embedding of ℤ -/

/-- The proposed embedding `n ↦ (1/2 + 1/(2n), |n|)`. -/
noncomputable def emb (n : ℤ) : ℝ × ℝ := (1 / 2 + 1 / (2 * (n : ℝ)), |(n : ℝ)|)










/-! ### Refuted: the proposed zero divisors -/




end MoebiusBand


