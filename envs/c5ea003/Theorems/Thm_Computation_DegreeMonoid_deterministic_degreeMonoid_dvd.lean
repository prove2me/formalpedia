-- Prove2me | Theorems.Thm_Computation_DegreeMonoid_deterministic_degreeMonoid_dvd
-- name    : Computation.DegreeMonoid.deterministic_degreeMonoid_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:42:06.337028+00:00
-- url     : https://prove2.me/theorems/ad29a040-eb74-4085-8ed4-4965bdb5b1e5
-- title:
--   Determinism forces an arithmetic progression.
-- statement:
--   **Determinism forces an arithmetic progression.**  The set of closed-computation lengths
--   of a state of a deterministic machine is exactly the set of multiples of a single number
--   (its period).
--
--   ```lean
--   theorem Computation.DegreeMonoid.deterministic_degreeMonoid_dvd{R : α → α → Prop} (hdet : Deterministic R) (a : α) :
--       ∃ d : ℕ, d ∈ degreeMonoid R a ∧ ∀ n : ℕ, n ∈ degreeMonoid R a ↔ d ∣ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/DegreeMonoidDeterminism.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/DegreeMonoidDeterminism.lean#L60

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

theorem Computation.DegreeMonoid.deterministic_degreeMonoid_dvd{R : α → α → Prop} (hdet : Deterministic R) (a : α) :
    ∃ d : ℕ, d ∈ degreeMonoid R a ∧ ∀ n : ℕ, n ∈ degreeMonoid R a ↔ d ∣ n := by sorry
