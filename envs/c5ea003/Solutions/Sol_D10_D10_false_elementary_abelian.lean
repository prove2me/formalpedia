-- Prove2me | solution 1 for D10.D10_false_elementary_abelian
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:02:20.976034+00:00
-- url     : https://prove2.me/submissions/230496bd-4f46-4e22-ae10-646f9dcd9258

-- Sol generated from NumberTheory/MolienBurnsideElementaryAbelian.lean
import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10
import Definitions.Def_NumberTheory_MolienBurnsideElementaryAbelian
import Theorems.Thm_D10_ea_fixCount_eq
import Theorems.Thm_D10_markOn_Xlines_top
import Theorems.Thm_D10_markOn_XregEA_top
import Theorems.Thm_D10_markOn_bot
import Theorems.Thm_D10_molien_eq_of_fixCount_eq

/-!
# D10 fails for every elementary abelian group of rank two

The companion file `Catalog.NumberTheory.MolienBurnsideD10` refutes Conjecture D10 with a
`decide`-checked example over the Klein four group.  Here we upgrade that single example to
an **infinite family**, one for each prime `p`, with a genuine (non-`decide`) proof:

for `E = (ℤ/p)²` put

* `Xlines p = ⊔_{ℓ ∈ ℙ¹(𝔽_p)} E/ℓ`, the disjoint union of the `p+1` transitive `E`-sets of
  size `p` (indexed by the `p+1` lines through the origin, i.e. by the projective line),
* `Xreg p  = E ⊔ (p fixed points)`.

Both have `p(p+1) = p² + p` elements.  We show they have the *same permutation character*
(hence the same Molien invariant at every subgroup), while their Burnside marks at `⊤` are
`0` and `p` respectively; so no scaling relates the two mark vectors.

The heart of the computation is the projective-line count `card_vanishing_lines`: a nonzero
vector of `𝔽_p²` lies on exactly one of the `p+1` lines — an input from the theory of finite
fields (uniqueness of `-a/b`), which is what makes the character values agree.
-/

open D10

open Finset


variable (p : ℕ) [Fact p.Prime]


















/-- Hence the Molien invariants agree at every subgroup of `(ℤ/p)²`. -/
theorem ea_molien_eq (H : Subgroup (EA p)) [Fintype H] :
    molien (Xlines p) H = molien (XregEA p) H :=
  molien_eq_of_fixCount_eq (ea_fixCount_eq p) H







open D10 in
theorem solution:
    (∀ (H : Subgroup (EA p)) [Fintype H], molien (Xlines p) H = molien (XregEA p) H) ∧
      ¬ ∃ c : ℚ, ∀ (H : Subgroup (EA p)) [Fintype H],
        (markOn (Xlines p) H : ℚ) = c * (markOn (XregEA p) H : ℚ) := by
  classical
  refine ⟨fun H _ => ea_molien_eq p H, ?_⟩
  rintro ⟨c, hc⟩
  have hp0 : (0 : ℚ) < p := by
    haveI := Fact.out (p := p.Prime)
    exact_mod_cast Nat.pos_of_ne_zero (Nat.Prime.ne_zero (Fact.out (p := p.Prime)))
  have hbot := hc ⊥
  rw [markOn_bot, markOn_bot] at hbot
  have hcards : (Fintype.card (Xlines p) : ℚ) = (Fintype.card (XregEA p) : ℚ) := by
    simp [Fintype.card_prod, Fintype.card_option, Fintype.card_sum, ZMod.card]
    ring
  rw [hcards] at hbot
  have hcardpos : (0 : ℚ) < (Fintype.card (XregEA p) : ℚ) := by
    have : Fintype.card (XregEA p) = p * p + p := by
      simp [Fintype.card_sum, Fintype.card_prod, ZMod.card]
    rw [this]
    have : (0 : ℚ) < (p : ℚ) * p + p := by positivity
    exact_mod_cast this
  have hc1 : c = 1 := by
    have hne : (Fintype.card (XregEA p) : ℚ) ≠ 0 := ne_of_gt hcardpos
    have h2 : (1 : ℚ) * (Fintype.card (XregEA p) : ℚ)
        = c * (Fintype.card (XregEA p) : ℚ) := by rw [one_mul]; exact hbot
    exact (mul_right_cancel₀ hne h2).symm
  have htop := hc ⊤
  rw [markOn_Xlines_top, markOn_XregEA_top, hc1, one_mul] at htop
  simp only [Nat.cast_zero] at htop
  exact absurd htop.symm (ne_of_gt hp0)
