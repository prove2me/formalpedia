-- Prove2me | solution 1 for D10.markOn_Xlines_top
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T10:58:55.489893+00:00
-- url     : https://prove2.me/submissions/48fb198b-3698-47d6-99ce-f0b458b76122

-- Sol generated from NumberTheory/MolienBurnsideElementaryAbelian.lean
import Mathlib
import Definitions.Def_NumberTheory_MolienBurnsideD10
import Definitions.Def_NumberTheory_MolienBurnsideElementaryAbelian

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
theorem solution: markOn (Xlines p) (⊤ : Subgroup (EA p)) = 0 := by
  classical
  rw [markOn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, i⟩ _ hfix
  have hone : (1 : ZMod p) ≠ 0 := by
    haveI := Fact.out (p := p.Prime)
    exact one_ne_zero
  cases i with
  | none =>
      have h := hfix ⟨Multiplicative.ofAdd ((0 : ZMod p), (1 : ZMod p)), Subgroup.mem_top _⟩
      rw [smul_Xlines] at h
      simp only [Prod.mk.injEq, eaChar, toAdd_ofAdd] at h
      exact hone (by linear_combination h.1)
  | some c =>
      have h := hfix ⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)), Subgroup.mem_top _⟩
      rw [smul_Xlines] at h
      simp only [Prod.mk.injEq, eaChar, toAdd_ofAdd] at h
      exact hone (by linear_combination h.1)
