-- Prove2me | Definitions.Def_Geometry_PeelStoppingTime
-- name    : Geometry_PeelStoppingTime
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:51.046161+00:00
-- url     : https://prove2.me/theorems/7dc29278-38da-4c49-b948-548c86b14b54
-- title:
--   Aether Catalog definitions — Geometry_PeelStoppingTime
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PeelStoppingTime`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PeelStoppingTime.lean by skeleton subtraction
import Mathlib
/-
# Peeling profiles, stopping times, and the rigidity of the pigeonhole bound

A *peeling process* is the abstract skeleton shared by a large family of
geometric arguments: one removes successive "layers" from a body and records
the remaining content.  Formally the data is a nonincreasing, nonnegative
sequence `size : ℕ → ℝ` (`PeelProfile`), whose successive differences
`peelGap` are the layer contents.

The classical *upper bound* half of the theory is a pigeonhole statement:
inside any window of `N` peeling steps there is a step whose layer content is
at most the average `peelRate = (size 0 - size N)/N`.  This file formalises
that half (`exists_peel_stopping_time`, `peelEstimate_error`,
`peel_gap_density`, `exists_peel_stable_window`) and then goes further, to the
question of *sharpness*:

* `peel_extremal_tfae` — a four-way equivalence showing that the pigeonhole
  bound is saturated exactly by the arithmetic (equipartition) profiles, and
  that saturation is equivalent to invariance of the gap function under the
  cyclic shift of `ZMod N`.  This is the rigidity statement that converts the
  inequality into a classification.
* `peel_gap_const_of_pretransitive` — the group-theoretic form: if *any* group
  acts pretransitively on the `N` peeling steps and the gap function is
  invariant, all gaps equal the average.  Symmetry forces extremality.

`Catalog/Geometry/PeelSymmetryConstruction.lean` supplies the matching
geometric family of actions (equal-volume shell peelings of Euclidean balls,
equivariant for the orthogonal group).

## Lab notes

Numerical sanity checks performed while developing the file (see
`ComputationalEvidence.md`): the extremal profile for `N = 4`, `A = 1` is
`1, 3/4, 1/2, 1/4, 0`, all gaps `1/4`; the "front-loaded" profile
`1, 0, 0, 0, 0` has gaps `1, 0, 0, 0`, minimum gap `0 < 1/4`, illustrating
that the pigeonhole bound is far from an equality in general and that the
rigidity statement really needs the *uniform* smallness hypothesis.
-/

namespace Catalog.Geometry.Peel

open Finset

/-! ## Peeling profiles -/

/-- A **peeling profile**: the residual content after `k` peeling steps.
Nonincreasing and nonnegative. -/
structure PeelProfile where
  /-- Residual content after `k` peeling steps. -/
  size : ℕ → ℝ
  /-- Peeling only removes content. -/
  anti : Antitone size
  /-- Content is nonnegative. -/
  nonneg : ∀ k, 0 ≤ size k

variable (P : PeelProfile) {N J M k : ℕ}

/-- The content of the `k`-th peeled layer. -/
def peelGap (P : PeelProfile) (k : ℕ) : ℝ := P.size k - P.size (k + 1)

/-- Total content removed during the first `N` peeling steps. -/
def peelBudget (P : PeelProfile) (N : ℕ) : ℝ := P.size 0 - P.size N

/-- Average layer content over the first `N` steps. -/
noncomputable def peelRate (P : PeelProfile) (N : ℕ) : ℝ := peelBudget P N / N






/-! ## The upper bound: existence of a good stopping time -/


/-- The **mean-field (linear) estimate** of the profile: the straight line from
`size 0` to `size N`. -/
noncomputable def peelEstimate (P : PeelProfile) (N k : ℕ) : ℝ :=
  P.size 0 - k * peelRate P N








/-! ## Density of good stopping times -/



/-! ## Stable windows: blocks of consecutive small layers -/

/-- The profile obtained by peeling in blocks of `J` steps. -/
def blockProfile (P : PeelProfile) (J : ℕ) : PeelProfile where
  size k := P.size (J * k)
  anti := fun _ _ h => P.anti (Nat.mul_le_mul_left J h)
  nonneg := fun _ => P.nonneg _


/-! ## Rigidity: the pigeonhole bound is saturated only by arithmetic profiles -/


/-! ## Symmetry forces extremality -/

/-- The gap function of a window of `N` steps, as a function on `Fin N`. -/
def gapFin (P : PeelProfile) (N : ℕ) : Fin N → ℝ := fun i => peelGap P i




/-! ## The matching family: equipartition profiles -/

/-- The **equipartition profile**: total content `A` removed in `N` equal
layers.  This is the extremal family for the stopping-time bound. -/
noncomputable def equipartitionProfile (A : ℝ) (hA : 0 ≤ A) (N : ℕ) : PeelProfile where
  size k := A * max 0 (1 - (k : ℝ) / (N : ℝ))
  anti := by
    intro a b hab
    have hcast : (a : ℝ) ≤ b := by exact_mod_cast hab
    have : (1 : ℝ) - b / N ≤ 1 - a / N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp
      · have hNR : (0 : ℝ) < N := by exact_mod_cast h
        have : (a : ℝ) / N ≤ b / N := by gcongr
        linarith
    have := max_le_max (le_refl (0 : ℝ)) this
    exact mul_le_mul_of_nonneg_left this hA
  nonneg := fun _ => mul_nonneg hA (le_max_left _ _)

variable {A : ℝ}










end Catalog.Geometry.Peel


