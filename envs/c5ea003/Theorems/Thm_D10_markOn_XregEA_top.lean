-- Prove2me | Theorems.Thm_D10_markOn_XregEA_top
-- name    : D10.markOn_XregEA_top
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:26:16.485124+00:00
-- url     : https://prove2.me/theorems/eec6c393-dbbc-4989-81a6-42fdf587d838
-- title:
--   Exactly the `p` added points of `E ⊔ (p points)` are `E`-fixed.
-- statement:
--   Exactly the `p` added points of `E ⊔ (p points)` are `E`-fixed.
--
--   ```lean
--   theorem D10.markOn_XregEA_top: markOn (XregEA p) (⊤ : Subgroup (EA p)) = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/MolienBurnsideElementaryAbelian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/MolienBurnsideElementaryAbelian.lean#L218

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

theorem D10.markOn_XregEA_top: markOn (XregEA p) (⊤ : Subgroup (EA p)) = p := by sorry
