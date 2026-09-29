-- Prove2me | solution 1 for ECAFixedVariety.iterate_eq_self_gcd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:05:28.873324+00:00
-- url     : https://prove2.me/submissions/2bbe1ba8-a61a-4b39-9f59-a00afa103570

-- Sol generated from Novelty/ECAPeriodicPointLattice.lean
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

/-- Return times are closed under addition of multiples. -/
lemma iterate_mul_eq_self {α : Type*} {f : α → α} {x : α} {k : ℕ} (hk : f^[k] x = x) :
    ∀ m : ℕ, f^[k * m] x = x := by
  intro m
  induction m with
  | zero => simp
  | succ p ih =>
      have : k * (p + 1) = k * p + k := by ring
      rw [this, Function.iterate_add_apply, hk, ih]


/-! ### The temporal varieties of an elementary cellular automaton -/








/-! ### The tower collapses for Rule 0 -/


/-! ### Rule 110 genuinely oscillates -/









open ECAFixedVariety in
theorem solution{α : Type*} {f : α → α} {x : α} :
    ∀ k l : ℕ, f^[k] x = x → f^[l] x = x → f^[Nat.gcd k l] x = x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro l hk hl
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using hl
    · -- `l = k * (l / k) + l % k`, so the remainder is also a return time
      have hrem : f^[l % k] x = x := by
        have h2 := hl
        rw [← Nat.mod_add_div l k, Function.iterate_add_apply, iterate_mul_eq_self hk] at h2
        exact h2
      have hlt : l % k < k := Nat.mod_lt _ hkpos
      have := ih (l % k) hlt k hrem hk
      rwa [← Nat.gcd_rec] at this
