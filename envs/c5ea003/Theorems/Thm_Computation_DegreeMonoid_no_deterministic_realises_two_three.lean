-- Prove2me | Theorems.Thm_Computation_DegreeMonoid_no_deterministic_realises_two_three
-- name    : Computation.DegreeMonoid.no_deterministic_realises_two_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:42:13.212149+00:00
-- url     : https://prove2.me/theorems/6429d74e-4e2f-4365-9a7f-41e9f51f1a1c
-- title:
--   Separation theorem.
-- statement:
--   **Separation theorem.**  No deterministic machine, on any state space, has the numerical
--   semigroup `⟨2,3⟩` as the degree monoid of a state: the Frobenius gap `1` is an intrinsic
--   witness of nondeterminism.
--
--   ```lean
--   theorem Computation.DegreeMonoid.no_deterministic_realises_two_three{R : α → α → Prop} (hdet : Deterministic R) (a : α) :
--       degreeMonoid R a ≠ AddSubmonoid.closure ({2, 3} : Set ℕ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/DegreeMonoidDeterminism.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/DegreeMonoidDeterminism.lean#L138

-- Thm stub generated from Speculative/AutoResearch/DegreeMonoidDeterminism.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidDeterminism
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
/-
# Determinism, gaps, and finite-state realisation of degree monoids

Two further layers on top of `Computation.DegreeMonoidRealisation` and
`Computation.DegreeMonoidStructure`.

**Determinism.**  For a *deterministic* transition relation the degree monoid of a state is
closed under subtraction, hence is the full arithmetic progression `dℕ`
(`deterministic_degreeMonoid_dvd`): a deterministic machine has **no gaps**
(`deterministic_no_gaps`).  Consequently the existence of a single gap is a certificate of
nondeterminism (`nondeterministic_of_gap`), and *no* deterministic machine — on any state
space whatsoever — can have the numerical semigroup `⟨2,3⟩` as its degree monoid
(`no_deterministic_realises_two_three`).  The invariant therefore separates deterministic
from nondeterministic computation.

**Finite state spaces.**  Using that every additive submonoid of `ℕ` is finitely generated,
the realisation theorem can be upgraded: every submonoid of `ℕ` is the degree monoid of a
state of a machine with *finitely many* states (`exists_finite_machine`), so finite
nondeterministic machines already realise the whole invariant lattice
(`finite_state_degreeMonoid_range`).

All results are proved with no `sorry`.
-/

open Computation
open DegreeMonoid

variable {α : Type*}

/-! ## Deterministic systems -/

theorem Computation.DegreeMonoid.no_deterministic_realises_two_three{R : α → α → Prop} (hdet : Deterministic R) (a : α) :
    degreeMonoid R a ≠ AddSubmonoid.closure ({2, 3} : Set ℕ) := by sorry
