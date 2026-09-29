-- Prove2me | solution 1 for ECAFixedVariety.step_bijOn_periodicSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:23:39.437006+00:00
-- url     : https://prove2.me/submissions/1de59d23-0445-4a51-84ea-158d442ed962

-- Sol generated from Novelty/ECAPeriodicPointLattice.lean
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








/-! ### The tower collapses for Rule 0 -/


/-! ### Rule 110 genuinely oscillates -/









open ECAFixedVariety in
theorem solution(rule n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Set.BijOn (step rule) (periodicSet rule n k) (periodicSet rule n k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hs' : (step rule)^[m + 1] s = s := hs
    show (step rule)^[m + 1] (step rule s) = step rule s
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hs']
  · intro a ha b hb hab
    have ha' : (step rule)^[m + 1] a = a := ha
    have hb' : (step rule)^[m + 1] b = b := hb
    have hiter : (step rule)^[m] (step rule a) = (step rule)^[m] (step rule b) := by rw [hab]
    rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply, ha', hb'] at hiter
    exact hiter
  · intro s hs
    have hs' : (step rule)^[m + 1] s = s := hs
    refine ⟨(step rule)^[m] s, ?_, ?_⟩
    · show (step rule)^[m + 1] ((step rule)^[m] s) = (step rule)^[m] s
      rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hs']
    · exact (Function.iterate_succ_apply' (step rule) m s).symm.trans hs'
