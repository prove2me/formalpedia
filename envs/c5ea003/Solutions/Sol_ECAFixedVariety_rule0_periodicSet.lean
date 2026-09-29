-- Prove2me | solution 1 for ECAFixedVariety.rule0_periodicSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:09:46.233774+00:00
-- url     : https://prove2.me/submissions/ba7117e0-be2b-493c-8e35-0b00abadb796

-- Sol generated from Novelty/ECAPeriodicPointLattice.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyNoDimension
import Definitions.Def_Novelty_ECAPeriodicPointLattice
import Theorems.Thm_ECAFixedVariety_rule0_localRuleZ

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
theorem solution{n k : ℕ} (hk : 1 ≤ k) : periodicSet 0 n k = {0} := by
  have hstep : ∀ s : Cfg n, step 0 s = 0 := by
    intro s
    funext i
    exact rule0_localRuleZ _ _ _
  have hiter : ∀ (m : ℕ) (s : Cfg n), (step 0)^[m + 1] s = 0 := by
    intro m
    induction m with
    | zero => intro s; simpa using hstep s
    | succ p ih => intro s; rw [Function.iterate_succ_apply]; exact ih _
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  ext s
  rw [Set.mem_singleton_iff]
  constructor
  · intro hs
    exact ((hiter m s).symm.trans hs).symm
  · rintro rfl
    show (step 0)^[m + 1] (0 : Cfg n) = 0
    exact hiter m 0
