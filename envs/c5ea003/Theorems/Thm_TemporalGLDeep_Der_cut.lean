-- Prove2me | Theorems.Thm_TemporalGLDeep_Der_cut
-- name    : TemporalGLDeep.Der_cut
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:55:11.426852+00:00
-- url     : https://prove2.me/theorems/5f6c41c8-d5d3-4fc2-91c3-739e374c54dd
-- title:
--   Cut: if every hypothesis of `Δ` is derivable from `Γ`, then anything derivable
-- statement:
--   **Cut**: if every hypothesis of `Δ` is derivable from `Γ`, then anything derivable
--   from `Δ` is derivable from `Γ`.
--
--   ```lean
--   theorem TemporalGLDeep.Der_cut{Γ Δ : List TForm} {X : TForm} (h : ∀ x ∈ Δ, Der Γ x) (hd : Der Δ X) :
--       Der Γ X := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/TemporalGLDeduction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/TemporalGLDeduction.lean#L88

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

theorem TemporalGLDeep.Der_cut{Γ Δ : List TForm} {X : TForm} (h : ∀ x ∈ Δ, Der Γ x) (hd : Der Δ X) :
    Der Γ X := by sorry
