-- Prove2me | solution 1 for D10.fixCount_Xlines
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T10:53:03.965109+00:00
-- url     : https://prove2.me/submissions/31fc5608-afec-4948-be96-612b7d08d530

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
    fixCount (Xlines p) g
      = p * (univ.filter fun i : Option (ZMod p) =>
          eaChar p i (Multiplicative.toAdd g) = 0).card := by
  classical
  rw [fixCount, Finset.card_filter, Fintype.sum_prod_type]
  have hterm : ∀ x : ZMod p, ∀ i : Option (ZMod p),
      (if g • ((x, i) : Xlines p) = (x, i) then 1 else 0)
        = (if eaChar p i (Multiplicative.toAdd g) = 0 then 1 else 0) := by
    intro x i
    congr 1
    rw [smul_Xlines]
    simp [Prod.ext_iff]
  simp only [hterm]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul,
    Finset.card_filter]
