-- Prove2me | Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
-- name    : Speculative_AutoResearch_DegreeMonoidStructure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:28:41.120127+00:00
-- url     : https://prove2.me/theorems/c459e9d2-01d4-49a4-ac04-e8b9f2de4940
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_DegreeMonoidStructure
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.DegreeMonoidStructure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/DegreeMonoidStructure.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
/-
# Structure theory of degree monoids: period, gaps and the Frobenius obstruction

`Computation.DegreeMonoidRealisation` shows that the degree monoid
`degreeMonoid R a ≤ ℕ` of a state of a transition system is a complete invariant for the
lattice of additive submonoids of `ℕ`: *every* submonoid is realised by the chain machine
`chainRel M`.  Completeness of a realisation problem is only half the story — the other
half is the *structure* of the realised objects.  This file supplies it:

* `degPeriod R a` — the period of a state, the gcd of all its closed-computation lengths;
* `degPeriod_dvd_mem` and `exists_ge_mem_degreeMonoid` — the **structure theorem**: every
  closed computation has length divisible by the period, and conversely *every*
  sufficiently large multiple of the period is a closed-computation length.  So the degree
  monoid is an eventually complete arithmetic progression;
* `degreeMonoid_gaps_finite` — a state has only finitely many *gaps* (multiples of the
  period which are not computation lengths);
* `degPeriod_eq_zero_iff` — the sharp dichotomy: period `0` exactly for the dead state
  (`degreeMonoid = ⊥`);
* `degPeriod_prodRel` — the **synchronisation law**: the period of a synchronous product of
  two live machines is the *least common multiple* of the two periods;
* `frobenius_gap_of_chainRel` — a number-theoretic bridge: for coprime `p, q > 1` the chain
  machine of `⟨p, q⟩` has largest gap exactly `p*q - p - q` (Chicken McNugget/Frobenius),
  and `frobenius_gap_two_three` specialises this to the certified sample value `⟨2,3⟩`,
  whose unique gap is the length `1`.

All results are proved with no `sorry`.
-/

namespace Computation
namespace DegreeMonoid

variable {α β : Type*}

/-! ## The period of a state -/

/-- The **period** of a state: the gcd of the lengths of all its closed computations
(`0` exactly when the only closed computation is the empty one). -/
noncomputable def degPeriod (R : α → α → Prop) (a : α) : ℕ :=
  Nat.setGcd (degreeMonoid R a : Set ℕ)







/-! ## Synchronisation: periods multiply to their lcm under products -/



/-! ## The Frobenius obstruction of a two-loop machine -/




end DegreeMonoid
end Computation


