-- Prove2me | Theorems.Thm_Computation_DegreeMonoid_degPeriod_chainRel_coprime
-- name    : Computation.DegreeMonoid.degPeriod_chainRel_coprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:41:12.074841+00:00
-- url     : https://prove2.me/theorems/fff464cd-5eb9-4b48-9d27-6faa1d8c8a35
-- title:
--   The period of the two-loop machine of coprime `p, q` is `1`: it is *aperiodic*, and by
-- statement:
--   The period of the two-loop machine of coprime `p, q` is `1`: it is *aperiodic*, and by
--   `frobenius_gap_of_chainRel` its finitely many gaps stop exactly at `p * q - p - q`.
--   (Coprimality alone suffices here; the bounds `1 < p`, `1 < q` are not needed.)
--
--   ```lean
--   theorem Computation.DegreeMonoid.degPeriod_chainRel_coprime{p q : ℕ} (cop : Nat.Coprime p q) :
--       degPeriod (chainRel ({p, q} : Set ℕ)) 0 = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/DegreeMonoidStructure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/DegreeMonoidStructure.lean#L177

-- Thm stub generated from Speculative/AutoResearch/DegreeMonoidStructure.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
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

open Computation
open DegreeMonoid

variable {α β : Type*}

/-! ## The period of a state -/








/-! ## Synchronisation: periods multiply to their lcm under products -/



/-! ## The Frobenius obstruction of a two-loop machine -/

theorem Computation.DegreeMonoid.degPeriod_chainRel_coprime{p q : ℕ} (cop : Nat.Coprime p q) :
    degPeriod (chainRel ({p, q} : Set ℕ)) 0 = 1 := by sorry
