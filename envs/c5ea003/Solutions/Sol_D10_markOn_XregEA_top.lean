-- Prove2me | solution 1 for D10.markOn_XregEA_top
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T10:58:55.954215+00:00
-- url     : https://prove2.me/submissions/cfeb2ca9-318e-4f8f-891c-402e135bf1b3

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
theorem solution: markOn (XregEA p) (⊤ : Subgroup (EA p)) = p := by
  classical
  rw [markOn, Finset.card_filter, Fintype.sum_sum_type]
  have hone : (1 : ZMod p) ≠ 0 := by
    haveI := Fact.out (p := p.Prime)
    exact one_ne_zero
  have hleft : ∀ q : ZMod p × ZMod p,
      (if ∀ h : (⊤ : Subgroup (EA p)), (h : EA p) • (Sum.inl q : XregEA p) = Sum.inl q
        then 1 else 0) = 0 := by
    intro q
    rw [if_neg]
    intro hfix
    have h := hfix ⟨Multiplicative.ofAdd ((1 : ZMod p), (0 : ZMod p)), Subgroup.mem_top _⟩
    rw [smul_XregEA_inl] at h
    simp only [Sum.inl.injEq] at h
    have h1 := congrArg Prod.fst h
    simp only [Prod.fst_add, toAdd_ofAdd] at h1
    exact hone (by linear_combination h1)
  have hright : ∀ c : ZMod p,
      (if ∀ h : (⊤ : Subgroup (EA p)), (h : EA p) • (Sum.inr c : XregEA p) = Sum.inr c
        then 1 else 0) = 1 := by
    intro c
    rw [if_pos]
    intro h
    exact smul_XregEA_inr p (h : EA p) c
  simp only [hleft, hright]
  simp [ZMod.card]
