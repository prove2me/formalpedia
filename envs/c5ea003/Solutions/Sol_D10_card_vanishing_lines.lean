-- Prove2me | solution 1 for D10.card_vanishing_lines
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T10:53:03.492177+00:00
-- url     : https://prove2.me/submissions/1ab824da-aafb-44c7-be0e-2fcec08caffd

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
theorem solution(v : ZMod p × ZMod p) (hv : v ≠ 0) :
    (univ.filter fun i : Option (ZMod p) => eaChar p i v = 0).card = 1 := by
  classical
  rcases eq_or_ne v.2 0 with h2 | h2
  · have h1 : v.1 ≠ 0 := by
      intro h1
      exact hv (Prod.ext h1 h2)
    refine Finset.card_eq_one.mpr ⟨none, ?_⟩
    ext i
    cases i with
    | none => simp [eaChar, h2]
    | some c => simp [eaChar, h2, h1]
  · refine Finset.card_eq_one.mpr ⟨some (-(v.1 / v.2)), ?_⟩
    ext i
    cases i with
    | none => simp [eaChar, h2]
    | some c =>
        simp only [mem_filter, mem_univ, true_and, eaChar, mem_singleton, Option.some.injEq]
        constructor
        · intro hc
          field_simp
          linear_combination hc
        · intro hc
          subst hc
          field_simp
          ring
