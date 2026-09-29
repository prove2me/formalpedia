-- Prove2me | Theorems.Thm_ECAFixedVariety_iterate_eq_self_gcd
-- name    : ECAFixedVariety.iterate_eq_self_gcd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:32:38.072785+00:00
-- url     : https://prove2.me/theorems/02b0a238-cb75-43d3-953b-329cdec777d9
-- title:
--   Return times are closed under `gcd`.
-- statement:
--   **Return times are closed under `gcd`.**  If a point returns after `k` steps
--   and after `l` steps, it returns after `gcd k l` steps.
--
--   ```lean
--   theorem ECAFixedVariety.iterate_eq_self_gcd{α : Type*} {f : α → α} {x : α} :
--       ∀ k l : ℕ, f^[k] x = x → f^[l] x = x → f^[Nat.gcd k l] x = x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAPeriodicPointLattice.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAPeriodicPointLattice.lean#L46

-- Thm stub generated from Novelty/ECAPeriodicPointLattice.lean
import Mathlib
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

theorem ECAFixedVariety.iterate_eq_self_gcd{α : Type*} {f : α → α} {x : α} :
    ∀ k l : ℕ, f^[k] x = x → f^[l] x = x → f^[Nat.gcd k l] x = x := by sorry
