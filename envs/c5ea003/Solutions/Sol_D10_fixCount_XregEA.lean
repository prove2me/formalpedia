-- Prove2me | solution 1 for D10.fixCount_XregEA
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T10:53:04.463864+00:00
-- url     : https://prove2.me/submissions/c285d52c-2be4-43e0-a369-c75029d27339

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
theorem solution(g : EA p) :
    fixCount (XregEA p) g
      = (if Multiplicative.toAdd g = 0 then p * p else 0) + p := by
  classical
  rw [fixCount, Finset.card_filter, Fintype.sum_sum_type]
  have hleft : ∀ q : ZMod p × ZMod p,
      (if g • (Sum.inl q : XregEA p) = Sum.inl q then 1 else 0)
        = (if Multiplicative.toAdd g = 0 then 1 else 0) := by
    intro q
    congr 1
    rw [smul_XregEA_inl]
    simp
  have hright : ∀ c : ZMod p,
      (if g • (Sum.inr c : XregEA p) = Sum.inr c then 1 else 0) = 1 := by
    intro c
    rw [smul_XregEA_inr, if_pos rfl]
  simp only [hleft, hright]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, ZMod.card,
    Fintype.card_prod, ZMod.card, smul_eq_mul, smul_eq_mul, mul_one]
  by_cases hg : Multiplicative.toAdd g = 0 <;> simp [hg]
