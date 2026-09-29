-- Prove2me | solution 1 for Bridges.TemporalComputation.singletonOrbit_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:02:09.246702+00:00
-- url     : https://prove2.me/submissions/b58fb8d4-14b0-4769-ac1c-4b252b84409c

-- Sol generated from Bridges/ReversibleFixedPointDuality.lean
import Mathlib
import Definitions.Def_Bridges_ReversibleFixedPointDuality
/-
# Temporal Fixed-Point Duality for Reversible Causal Semirings

This file formalizes a duality between reversible finite-state dynamics,
temporal fixed-point semantics, and certified loop invariant reconstruction.

## Main Results

### Reversible Dynamics (§1-§2)
- `bijective_dynamics_purely_periodic` — Bijections on finite types yield purely periodic orbits
- `iterate_eq_iff_period_dvd` — f^[k] x = x iff period divides k

### Temporal Fixed-Point Operators (§3-§4)
- `temporalReach_monotone` — The temporal reachability operator is monotone
- `temporalCoreach_monotone` — The temporal co-reachability operator is monotone

### Orbit-Fixed-Point Correspondence (§5)
- `periodic_orbit_is_lfp_gfp_pair` — Periodic orbits are minimal invariant sets

### Temporal Congruence (§6)
- `temporalCongruence_is_right_congruence` — Temporal congruence preserved by transitions

### Loop Invariant Reconstruction (§7)
- `certified_loop_invariant_reconstruction` — Certified forward/backward invariants

### Bisimulation Invariance (§9)
- `bisimulation_period_divides` — Periods divide under bisimulation
- `fixedPointSpectrum_coarser_under_bisim` — Spectrum coarsens under bisimulation

## Bridges
- **Algebra ↔ Logic**: Knaster-Tarski fixed points ↔ temporal μ/ν-calculus
- **Logic ↔ Computation**: Temporal congruence ↔ automata minimization
- **Computation ↔ Algebra**: Loop invariants ↔ idempotent semiring dynamics
-/


open Function Finset

noncomputable section

open Bridges.TemporalComputation

/-! ## §1. Reversible Finite-State Dynamics -/


variable {S : Type*} [Fintype S] [DecidableEq S]


/-! ## §2. Pure Periodicity of Reversible Dynamics -/

/-
On a finite type, a bijective map yields purely periodic orbits:
    there exists p > 0 such that f^[p] x = x. This is strictly stronger
    than `finite_dynamics_eventually_periodic` which only gives f^[m] = f^[n].

    Bridge: connects reversible computation to temporal logic via periodicity.
-/

/-
f^[k] x = x iff the minimal period divides k, for bijections on finite types.
-/

/-
For bijections on finite types, the minimal period is positive.
-/

/-! ## §3. Temporal Fixed-Point Operators on Finsets -/







/-! ## §4. Invariant Sets and Their Characterization -/


/-
A set is T-invariant iff it is a fixed point of the co-reachability operator.
    Bridge: algebraic (semiring) viewpoint ↔ logical (fixed point) viewpoint.
-/

/-
For a bijection, invariant set has f-image equal to itself.
-/

/-
For a bijection, any invariant set is backward-invariant.
-/


/-! ## §5. Periodic Orbits as Minimal Invariant Sets -/



/-
The singleton orbit is T-invariant.
-/

/-
**Orbit minimality theorem**: The orbit of x under a bijection is the
    smallest invariant set containing x.

    Bridge: Knaster-Tarski (Algebra) ↔ μ-calculus reachability (Logic)
    ↔ minimal automaton states (Computation).
-/


/-! ## §6. Temporal Congruence -/





/-! ## §7. Loop Invariants from Fixed Points -/



/-
The complement of an invariant set of a bijection is also invariant.
    Bridge: reversible dynamics ↔ dual loop invariants (safety + liveness).
-/



/-! ## §8. Idempotent Semiring Structure -/




/-! ## §9. Bisimulation Invariance of the Spectrum -/



/-
Under a bisimulation, periods in the codomain divide those in the domain.
    Bridge: the period spectrum is a bisimulation semi-invariant.
-/


/-! ## §10. The Full Duality Theorem -/



open Bridges.TemporalComputation in
theorem solution(f : S → S) (hf : Bijective f) (x : S) :
    Bridges.TemporalComputation.IsInvariant f (singletonOrbit f x) := by
  unfold Bridges.TemporalComputation.IsInvariant;
  simp +decide [ singletonOrbit, Finset.subset_iff ];
  -- Since $f$ is bijective, its forward orbit is finite and thus must eventually repeat.
  have h_orbit_finite : ∃ p : ℕ, 0 < p ∧ p ≤ Fintype.card S ∧ f^[p] x = x := by
    -- By the pigeonhole principle, since there are only $|S|$ possible values for $f^k(x)$, there must be some $i < j \leq |S|$ such that $f^i(x) = f^j(x)$.
    obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card S ∧ f^[i] x = f^[j] x := by
      by_contra! h;
      exact absurd ( Finset.card_le_univ ( Finset.image ( fun i => f^[i] x ) ( Finset.range ( Fintype.card S + 1 ) ) ) ) ( by rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( not_lt.1 fun hi' => h _ _ hi' ( by linarith [ Finset.mem_range.1 hi, Finset.mem_range.1 hj ] ) hij.symm ) ( not_lt.1 fun hj' => h _ _ hj' ( by linarith [ Finset.mem_range.1 hi, Finset.mem_range.1 hj ] ) hij ) ] ; simp +decide );
    refine' ⟨ j - i, tsub_pos_of_lt hij, _, _ ⟩;
    · exact le_trans ( Nat.sub_le _ _ ) h_eq.1;
    · rw [ ← Nat.add_sub_of_le hij.le, Function.iterate_add_apply ] at h_eq;
      exact hf.injective.iterate i h_eq.2.symm;
  intro a ha
  obtain ⟨p, hp_pos, hp_le, hp_eq⟩ := h_orbit_finite
  have hp_iter : ∀ k : ℕ, f^[p * k] x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hmul : p * (k + 1) = p * k + p := by ring
      rw [hmul, Function.iterate_add_apply, hp_eq]
      exact ih
  have h_orbit_step : f^[a + 1] x = f^[ (a + 1) % p ] x := by
    have h1 : (a + 1) % p + p * ((a + 1) / p) = a + 1 := Nat.mod_add_div (a + 1) p
    conv_lhs => rw [← h1]
    rw [Function.iterate_add_apply, hp_iter]
  exact ⟨ ( a + 1 ) % p, lt_of_lt_of_le ( Nat.mod_lt _ hp_pos ) hp_le, by simpa [ ← Function.iterate_succ_apply' ] using h_orbit_step.symm ⟩
