-- Prove2me | Theorems.Thm_ECAFixedVariety_step_bijOn_periodicSet
-- name    : ECAFixedVariety.step_bijOn_periodicSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:34:34.263419+00:00
-- url     : https://prove2.me/theorems/f52292ab-f322-40e3-b87d-b234a9caf001
-- title:
--   The automaton acts bijectively on every temporal variety: on `Per_k` the
-- statement:
--   The automaton acts bijectively on every temporal variety: on `Per_k` the
--   inverse of `step` is `step^{k-1}`.
--
--   ```lean
--   theorem ECAFixedVariety.step_bijOn_periodicSet(rule n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
--       Set.BijOn (step rule) (periodicSet rule n k) (periodicSet rule n k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAPeriodicPointLattice.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAPeriodicPointLattice.lean#L101

-- Thm stub generated from Novelty/ECAPeriodicPointLattice.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyNoDimension
import Definitions.Def_Novelty_ECAPeriodicPointLattice

/-!
# Cycle 2: the periodic-point lattice, a working replacement for the dimension

Cycle 1 showed that the fixed-point variety `V(f)` is blind to Wolfram
complexity: the Turing-complete Rule 110 and the null Rule 0 have *identical*
fixed loci.  The natural repair is to replace the single variety `V(f)` by the
whole tower of *temporal* varieties

  `Per_k(f) = { s : f^k(s) = s }`,

the `𝔽₂`-points of the fixed locus of the `k`-fold composite (a polynomial map
of degree `3^k`), i.e. the coefficients of the dynamical zeta function.

## Main results

* `iterate_eq_self_gcd` — a purely dynamical, number-theoretic lemma: the
  return times of a point are closed under `gcd`.
* `periodicSet_inter` — hence the tower is a **lattice under divisibility**:
  `Per_k ∩ Per_l = Per_{gcd(k,l)}`, and `periodicSet_mono_of_dvd` gives the
  order relation.
* `step_bijOn_periodicSet` — the automaton acts bijectively on each `Per_k`.
* `rule0_periodicSet` — the whole tower of the null rule collapses to a point.
* `rule110_two_cycle_mem`, `periodicSet_separates_rule110_rule0` — Rule 110 has a
  genuine `2`-cycle already on the ring of size `4`, so the tower **does**
  separate Rule 110 from Rule 0, unlike the fixed-point variety alone.
* `rule110_periodicSet_two_ncard`, `rule110_periodicSet_not_affine` — that
  temporal variety has `5` points, so it is not an affine subvariety either:
  even the repaired invariant is not a "dimension".
-/

open ECAFixedVariety

/-! ### The return-time lattice of an arbitrary self-map -/



/-! ### The temporal varieties of an elementary cellular automaton -/

theorem ECAFixedVariety.step_bijOn_periodicSet(rule n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Set.BijOn (step rule) (periodicSet rule n k) (periodicSet rule n k) := by sorry
