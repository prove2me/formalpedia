-- Prove2me | Theorems.Thm_Computation_DegreeMonoid_exists_finite_machine
-- name    : Computation.DegreeMonoid.exists_finite_machine
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:41:52.008901+00:00
-- url     : https://prove2.me/theorems/7d94d706-27bb-4c25-99d1-6ce604027b34
-- title:
--   Finite-state realisation theorem.
-- statement:
--   **Finite-state realisation theorem.**  Every additive submonoid of `ℕ` is the degree
--   monoid of a state of a machine with only finitely many states.  (The state bound comes from
--   finite generation of submonoids of `ℕ`; nondeterminism is essential by
--   `no_deterministic_realises_two_three`.)
--
--   ```lean
--   theorem Computation.DegreeMonoid.exists_finite_machine(M : AddSubmonoid ℕ) :
--       ∃ (B : ℕ) (R : Fin (B + 1) → Fin (B + 1) → Prop) (a : Fin (B + 1)),
--         degreeMonoid R a = M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/DegreeMonoidDeterminism.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/DegreeMonoidDeterminism.lean#L201

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









/-! ## Determinism on a finite state space bounds the period -/


/-! ## Finite-state realisation -/

theorem Computation.DegreeMonoid.exists_finite_machine(M : AddSubmonoid ℕ) :
    ∃ (B : ℕ) (R : Fin (B + 1) → Fin (B + 1) → Prop) (a : Fin (B + 1)),
      degreeMonoid R a = M := by sorry
