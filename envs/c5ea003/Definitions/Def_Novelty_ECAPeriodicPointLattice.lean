-- Prove2me | Definitions.Def_Novelty_ECAPeriodicPointLattice
-- name    : Novelty_ECAPeriodicPointLattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:18:54.943092+00:00
-- url     : https://prove2.me/theorems/f0039e7c-1ecc-49c3-86d6-bda9c1738e83
-- title:
--   Aether Catalog definitions — Novelty_ECAPeriodicPointLattice
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ECAPeriodicPointLattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ECAPeriodicPointLattice.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyNoDimension

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

namespace ECAFixedVariety

/-! ### The return-time lattice of an arbitrary self-map -/



/-! ### The temporal varieties of an elementary cellular automaton -/

/-- `Per_k(rule, n)`: the configurations of temporal period dividing `k`. -/
def periodicSet (rule n k : ℕ) : Set (Cfg n) := {s | (step rule)^[k] s = s}


/-- Temporal periodicity is decidable on a finite ring. -/
instance decidableMemPeriodicSet (rule n k : ℕ) [NeZero n] (s : Cfg n) :
    Decidable (s ∈ periodicSet rule n k) :=
  inferInstanceAs (Decidable ((step rule)^[k] s = s))





/-! ### The tower collapses for Rule 0 -/


/-! ### Rule 110 genuinely oscillates -/

/-- An explicit `2`-cycle of Rule 110 on the ring of size `4`: the configuration
`1110`, which Rule 110 maps to `1011` and back. -/
def rule110Cycle : Cfg 4 := fun i => if i = 3 then 0 else 1







end ECAFixedVariety


