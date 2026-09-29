-- Prove2me | solution 1 for ParkingFunctionPolytope.affineDilate_preserves_parking
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:32:08.142522+00:00
-- url     : https://prove2.me/submissions/7fda4407-2f05-406e-bffc-cca3088f0aba

-- Sol generated from Cryptography/ParkingFunctionPolytopes/Core.lean
import Mathlib
import Definitions.Def_Cryptography_GeometricCryptanalysis
import Definitions.Def_Cryptography_ParkingFunctionPolytopes_Core
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Generalized parking functions: profiles, slices, and lattice witnesses

A cumulative profile records the partial sums of the positive parameter vector
of a generalized parking function.  The definition below retains the permutation
that sorts the entries; this makes the chamber structure of the parking-function
polytope explicit.

The principal result is a lattice-slice theorem at the level of sorted chambers:
a coordinate of rank `r` can be deleted, and the remaining point is governed by
the profile obtained by deleting the same rank.  We also establish monotonicity
under enlargement of the cumulative profile, an affine dilation operation, and
a bridge from the bounding box of a parking-function polytope to short modular
kernel vectors.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer), ranked by expected impact:
1. Fixed labelled-coordinate lattice slices glue rank-deletion chambers into a
   single generalized parking-function polytope.
2. The chamber decomposition induces a shelling whose local contributions explain
   coefficientwise positivity of the Ehrhart polynomial.
3. Parking-profile boxes yield structured short vectors for modular syndrome maps,
   improving an unstructured pigeonhole radius when the matrix respects rank order.
4. Affine dilation about the all-ones vector is compatible with the integer-decomposition
   property of every generalized parking-function polytope.
5. Profile enlargement defines a functorial filtration whose successive differences
   have positive mixed-volume formulas.
6. Rank deletion commutes with affine dilation and generates a deletion recursion for
   lattice-point counts.

Experiment (Experimenter): cumulative profiles were tested in dimensions one
through four.  Deleting the same rank from a sorted vector and its profile always
preserved all coordinate inequalities.  The affine map `x ↦ 1 + t(x-1)` preserved
both order and positivity for every natural dilation factor `t`.

Analysis (Analyst): rank deletion, profile enlargement, and affine transport all
survive without convexity assumptions.  The full convex-hull identification of a
fixed labelled-coordinate slice additionally requires gluing the sorted chambers;
that geometric step is not asserted here.

Critique (Critic): the slice result is not a definitional equality: it composes a
sorting permutation with the order embedding that skips a rank.  The cryptographic
corollary genuinely invokes a finite pigeonhole theorem for modular syndromes.
The zero-dimensional edge case is isolated by using dimension `n+1` whenever a
largest profile value is required.

Synthesis (Principal Investigator): cumulative profiles provide a common language
for parking inequalities, lattice slices, affine dilations, and bounded-search
lattice attacks.
-- !-- Lab Notes -- !--
-/

open Finset BigOperators

open ParkingFunctionPolytope












open ParkingFunctionPolytope in
theorem solution{n : ℕ} (p : Profile n) (x : Fin n → ℕ)
    (t : ℕ) (hx : IsParking p x) :
    ∃ q : Profile n,
      (q.bound = fun i => affineDilate t (p.bound i)) ∧
      IsParking q (fun i => affineDilate t (x i)) := by
  let q : Profile n :=
    { bound := fun i => affineDilate t (p.bound i)
      positive := fun i => by simp [affineDilate]
      monotone := by
        intro i j hij
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_left t (Nat.sub_le_sub_right (p.monotone hij) 1)) 1 }
  refine ⟨q, rfl, ?_⟩
  rcases hx with ⟨σ, hmono, hbound⟩
  refine ⟨σ, ?_, ?_⟩
  · intro i j hij
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left t (Nat.sub_le_sub_right (hmono hij) 1)) 1
  · intro i
    constructor
    · simp [affineDilate]
    · exact Nat.add_le_add_left
        (Nat.mul_le_mul_left t (Nat.sub_le_sub_right (hbound i).2 1)) 1
