-- Prove2me | Theorems.Thm_TemporalGLDeep_Der_mono
-- name    : TemporalGLDeep.Der_mono
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:54:31.376611+00:00
-- url     : https://prove2.me/theorems/69d6cdd9-d451-42e0-bce0-223178439103
-- title:
--   Der mono
-- statement:
--   Formal statement of `TemporalGLDeep.Der_mono` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TemporalGLDeep.Der_mono{Γ₁ Γ₂ : List TForm} {X : TForm} (hs : ∀ x ∈ Γ₁, x ∈ Γ₂) (h : Der Γ₁ X) :
--       Der Γ₂ X := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/TemporalGLDeduction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/TemporalGLDeduction.lean#L73

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

theorem TemporalGLDeep.Der_mono{Γ₁ Γ₂ : List TForm} {X : TForm} (hs : ∀ x ∈ Γ₁, x ∈ Γ₂) (h : Der Γ₁ X) :
    Der Γ₂ X := by sorry
