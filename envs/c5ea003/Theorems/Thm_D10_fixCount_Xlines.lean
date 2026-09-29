-- Prove2me | Theorems.Thm_D10_fixCount_Xlines
-- name    : D10.fixCount_Xlines
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:25:32.310162+00:00
-- url     : https://prove2.me/theorems/b62c81bd-854c-4158-80fa-c97e44e8f019
-- title:
--   FixCount Xlines
-- statement:
--   Formal statement of `D10.fixCount_Xlines` from the Aether Catalog (NumberTheory). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem D10.fixCount_Xlines(g : EA p) :
--       fixCount (Xlines p) g
--         = p * (univ.filter fun i : Option (ZMod p) =>
--             eaChar p i (Multiplicative.toAdd g) = 0).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/MolienBurnsideElementaryAbelian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/MolienBurnsideElementaryAbelian.lean#L135

-- Thm stub generated from NumberTheory/MolienBurnsideElementaryAbelian.lean
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

theorem D10.fixCount_Xlines(g : EA p) :
    fixCount (Xlines p) g
      = p * (univ.filter fun i : Option (ZMod p) =>
          eaChar p i (Multiplicative.toAdd g) = 0).card := by sorry
