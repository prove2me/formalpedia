-- Prove2me | Definitions.Def_Speculative_AutoResearch_DegreeMonoidDeterminism
-- name    : Speculative_AutoResearch_DegreeMonoidDeterminism
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:10.719061+00:00
-- url     : https://prove2.me/theorems/b8359e5d-0430-4362-bd0d-da76925d76b6
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_DegreeMonoidDeterminism
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.DegreeMonoidDeterminism`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/DegreeMonoidDeterminism.lean by skeleton subtraction
import Mathlib
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

namespace Computation
namespace DegreeMonoid

variable {α : Type*}

/-! ## Deterministic systems -/

/-- A transition relation is **deterministic** when each state has at most one successor. -/
def Deterministic (R : α → α → Prop) : Prop := ∀ a b c : α, R a b → R a c → b = c








/-! ## Determinism on a finite state space bounds the period -/


/-! ## Finite-state realisation -/



end DegreeMonoid
end Computation


