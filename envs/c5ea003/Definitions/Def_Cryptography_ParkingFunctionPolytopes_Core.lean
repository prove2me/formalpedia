-- Prove2me | Definitions.Def_Cryptography_ParkingFunctionPolytopes_Core
-- name    : Cryptography_ParkingFunctionPolytopes_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:21:58.521739+00:00
-- url     : https://prove2.me/theorems/3ffcbfd8-fd0d-4f8d-859c-10645caecf70
-- title:
--   Aether Catalog definitions — Cryptography_ParkingFunctionPolytopes_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ParkingFunctionPolytopes.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ParkingFunctionPolytopes/Core.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_GeometricCryptanalysis
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

namespace ParkingFunctionPolytope

/-- A cumulative parking profile: positive, nondecreasing rank bounds. -/
structure Profile (n : ℕ) where
  bound : Fin n → ℕ
  positive : ∀ i, 0 < bound i
  monotone : Monotone bound

/-- A vector is admitted by a profile when some permutation puts it in
nondecreasing order and every entry then lies below its rank bound. -/
def IsParking {n : ℕ} (p : Profile n) (x : Fin n → ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    Monotone (fun i => x (σ i)) ∧
    ∀ i, 0 < x (σ i) ∧ x (σ i) ≤ p.bound i

/-- Restrict a profile to all ranks except `r`. -/
def Profile.erase {n : ℕ} (p : Profile (n + 1)) (r : Fin (n + 1)) : Profile n where
  bound i := p.bound (r.succAbove i)
  positive := fun i => p.positive (r.succAbove i)
  monotone := p.monotone.comp (Fin.succAboveOrderEmb r).monotone




/-- Affine dilation about the all-ones vector.  This is the integral map underlying
translation of dilates of parking-function polytopes. -/
def affineDilate (t x : ℕ) : ℕ := 1 + t * (x - 1)




end ParkingFunctionPolytope


