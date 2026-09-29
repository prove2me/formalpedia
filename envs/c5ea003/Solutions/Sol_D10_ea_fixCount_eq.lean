-- Prove2me | solution 1 for D10.ea_fixCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T10:58:55.04222+00:00
-- url     : https://prove2.me/submissions/429f4b69-8e44-4b81-a1de-e7628c505138

-- Sol generated from NumberTheory/MolienBurnsideElementaryAbelian.lean
import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10
import Definitions.Def_NumberTheory_MolienBurnsideElementaryAbelian
import Theorems.Thm_D10_card_vanishing_lines
import Theorems.Thm_D10_fixCount_Xlines
import Theorems.Thm_D10_fixCount_XregEA

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

























open D10 in
theorem solution(g : EA p) : fixCount (Xlines p) g = fixCount (XregEA p) g := by
  classical
  rw [fixCount_Xlines, fixCount_XregEA]
  rcases eq_or_ne (Multiplicative.toAdd g) 0 with h0 | h0
  · rw [if_pos h0, h0]
    have hall : (univ.filter fun i : Option (ZMod p) => eaChar p i 0 = 0) = univ := by
      apply Finset.filter_true_of_mem
      intro i _
      simp
    rw [hall, Finset.card_univ]
    simp [Fintype.card_option, ZMod.card]
    ring
  · rw [if_neg h0, card_vanishing_lines p _ h0]
    ring
