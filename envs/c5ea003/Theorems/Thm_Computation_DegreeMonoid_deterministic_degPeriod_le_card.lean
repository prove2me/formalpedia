-- Prove2me | Theorems.Thm_Computation_DegreeMonoid_deterministic_degPeriod_le_card
-- name    : Computation.DegreeMonoid.deterministic_degPeriod_le_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:42:16.499706+00:00
-- url     : https://prove2.me/theorems/ad6d3640-f3d0-429c-80ef-a89606802440
-- title:
--   Period bound for deterministic finite machines.
-- statement:
--   **Period bound for deterministic finite machines.**  On a finite state space a
--   deterministic machine with a nonempty closed computation has period at most the number of
--   states: the whole loop through the state consists of pairwise distinct states.
--
--   ```lean
--   theorem Computation.DegreeMonoid.deterministic_degPeriod_le_card[Fintype α] {R : α → α → Prop}
--       (hdet : Deterministic R) (a : α) (hlive : ∃ n ∈ degreeMonoid R a, n ≠ 0) :
--       degPeriod R a ≤ Fintype.card α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/DegreeMonoidDeterminism.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/DegreeMonoidDeterminism.lean#L161

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

theorem Computation.DegreeMonoid.deterministic_degPeriod_le_card[Fintype α] {R : α → α → Prop}
    (hdet : Deterministic R) (a : α) (hlive : ∃ n ∈ degreeMonoid R a, n ≠ 0) :
    degPeriod R a ≤ Fintype.card α := by sorry
