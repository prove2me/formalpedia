-- Prove2me | Theorems.Thm_D10_D10_false_elementary_abelian
-- name    : D10.D10_false_elementary_abelian
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:26:17.144642+00:00
-- url     : https://prove2.me/theorems/5f072e7f-2f45-4d33-bb62-996640075296
-- title:
--   D10 fails for every elementary abelian group of rank two.
-- statement:
--   **D10 fails for every elementary abelian group of rank two.**  For each prime `p` the
--   `(ℤ/p)²`-sets `Xlines p` and `XregEA p` have equal Molien invariants at every subgroup, but
--   their mark vectors are not proportional: the mark at `⊥` forces the scalar to be `1` while
--   the mark at `⊤` forces it to be `0`.
--
--   ```lean
--   theorem D10.D10_false_elementary_abelian:
--       (∀ (H : Subgroup (EA p)) [Fintype H], molien (Xlines p) H = molien (XregEA p) H) ∧
--         ¬ ∃ c : ℚ, ∀ (H : Subgroup (EA p)) [Fintype H],
--           (markOn (Xlines p) H : ℚ) = c * (markOn (XregEA p) H : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/MolienBurnsideElementaryAbelian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/MolienBurnsideElementaryAbelian.lean#L247

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

theorem D10.D10_false_elementary_abelian:
    (∀ (H : Subgroup (EA p)) [Fintype H], molien (Xlines p) H = molien (XregEA p) H) ∧
      ¬ ∃ c : ℚ, ∀ (H : Subgroup (EA p)) [Fintype H],
        (markOn (Xlines p) H : ℚ) = c * (markOn (XregEA p) H : ℚ) := by sorry
