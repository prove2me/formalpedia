-- Prove2me | Theorems.Thm_TemporalGLDeep_Der_case
-- name    : TemporalGLDeep.Der_case
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:54:26.640427+00:00
-- url     : https://prove2.me/theorems/1e65f205-12fa-4816-878e-8857de260732
-- title:
--   Case analysis on a formula and its negation.
-- statement:
--   **Case analysis** on a formula and its negation.
--
--   ```lean
--   theorem TemporalGLDeep.Der_case{Γ : List TForm} {B X : TForm} (h₁ : Der (B :: Γ) X)
--       (h₂ : Der (B.neg :: Γ) X) : Der Γ X := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/TemporalGLDeduction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/TemporalGLDeduction.lean#L103

-- Thm stub generated from Logic/PosetTheory/TemporalGLDeduction.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax

/-!
# Temporal Gödel–Löb logic: derivations from finite hypothesis lists

Working towards completeness of the calculus `TemporalGLDeep.Derivable`, this file sets
up the usual "sequent-like" interface on top of the Hilbert calculus:

`Der Γ X` means `⊢ x₁ ⟹ x₂ ⟹ ⋯ ⟹ xₙ ⟹ X` for `Γ = [x₁, …, xₙ]`.

Because the calculus takes *all* classical propositional tautologies as axioms, all the
propositional bookkeeping (weakening, cut, modus ponens, case analysis) reduces to the
single evaluation lemma `evalProp_implFold`, which is what `Der_taut_conseq` and
`Der_of_Der_taut` package.  The genuinely modal content is in

* `Der_box` : `Der Δ X → Der (Δ.map ◻) (◻X)` — necessitation plus iterated `K`,
* `Der_glob` : the temporal analogue,

both obtained from the distribution lemmas `boxDistrib` / `globDistrib`, proved by
induction on the hypothesis list.
-/

open TemporalGLDeep

/-! ## 1. Hypothesis lists -/

theorem TemporalGLDeep.Der_case{Γ : List TForm} {B X : TForm} (h₁ : Der (B :: Γ) X)
    (h₂ : Der (B.neg :: Γ) X) : Der Γ X := by sorry
