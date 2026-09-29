-- Prove2me | Theorems.Thm_LatticeEnumerator_subset_of_shiftCount_eq
-- name    : LatticeEnumerator.subset_of_shiftCount_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:52:54.967798+00:00
-- url     : https://prove2.me/theorems/a86cdfdb-f556-4ef8-b919-d28f6403e02f
-- title:
--   If the enumerators of all real translates of `P` dominate those of `Q` (here: agree),
-- statement:
--   If the enumerators of all real translates of `P` dominate those of `Q` (here: agree),
--   then `P ⊆ Q`.  The mechanism: for `t` small the periodisation `y ↦ |t(P+y) ∩ ℤ^d|` sees a
--   single lattice point, so it is the indicator of `P` up to a reflection.
--
--   ```lean
--   theorem LatticeEnumerator.subset_of_shiftCount_eq{P Q : Set (Fin d → ℝ)} (hbP : Bornology.IsBounded P)
--       (hbQ : Bornology.IsBounded Q)
--       (h : ∀ t : ℝ, 0 < t → ∀ y : Fin d → ℝ, shiftCount P t y = shiftCount Q t y) : P ⊆ Q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LatticePointEnumerator.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LatticePointEnumerator.lean#L331

-- Thm stub generated from Cryptography/LatticePointEnumerator.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator

/-!
# Lattice-point enumerators: asymptotics and rigidity

This file formalises the analytic core of the theory of *lattice-point enumerators*
`L_P(t) = |tP ∩ ℤ^d|` (`t > 0` a **real** dilation parameter) for bounded sets
`P ⊆ ℝ^d`, in the setting of the paper *A Fourier-analytic uniqueness theorem for
lattice-point enumerators*.

## Main definitions

* `LatticeEnumerator.shiftLattice P t y` : the set `{k ∈ ℤ^d : k/t - y ∈ P}` of lattice
  points of the dilated translate `t·(P + y)`.
* `LatticeEnumerator.dilLattice P t` : the lattice points `tP ∩ ℤ^d` (the case `y = 0`).
* `LatticeEnumerator.dilCount P t` : the lattice-point enumerator `L_P(t) = |tP ∩ ℤ^d|`.
* `LatticeEnumerator.shiftCount P t y` : the translated enumerator `|t(P + y) ∩ ℤ^d|`.
* `LatticeEnumerator.cube t k`, `LatticeEnumerator.floorMap t`,
  `LatticeEnumerator.approxSet P t` : the half-open `1/t`-cube attached to a lattice point,
  the coordinatewise rounding map `x ↦ ⌊t x⌋ / t`, and the union of the cubes attached to
  the counted lattice points.

## Main results

* `LatticeEnumerator.volume_approxSet` : the *exact* geometric identity
  `vol(A_t) = L_P(t) · t^{-d}`, where `A_t = {x : ⌊tx⌋/t ∈ P}` is a union of `L_P(t)`
  pairwise disjoint cubes of side `1/t`.
* `LatticeEnumerator.tendsto_dilCount_div` : the Gauss–Weyl counting theorem
  `L_P(t)/t^d → vol(P)` as `t → ∞`, for every bounded set with null topological frontier
  (Jordan measurable set).  The proof combines the exact identity above with dominated
  convergence, the domination coming from the fact that all the sets `A_t`, `t ≥ 1`, live
  in one fixed ball.
* `LatticeEnumerator.volume_eq_of_dilCount_eq` : two bounded Jordan measurable sets with
  the same real-parameter enumerator have the same volume.
* `LatticeEnumerator.volume_eq_of_dilCount_eq_convex` : the same statement for convex
  bodies, where Jordan measurability is automatic.
* `LatticeEnumerator.eq_of_shiftCount_eq` : a rigidity theorem.  If the enumerators of
  **all real translates** of two bounded sets agree, the sets are *equal* (not merely equal
  almost everywhere).  This isolates exactly where the difficulty of the integer-translate
  theorem lies: with real translates the periodisation is faithful at small `t`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

open LatticeEnumerator

variable {d : ℕ}

/-! ## Definitions -/










/-! ## Finiteness of the counted lattice sets -/




/-! ## The cube decomposition -/









/-! ## The rounding map and pointwise convergence -/




/-! ## The Gauss–Weyl counting theorem -/




/-! ## Rigidity for real translates -/

theorem LatticeEnumerator.subset_of_shiftCount_eq{P Q : Set (Fin d → ℝ)} (hbP : Bornology.IsBounded P)
    (hbQ : Bornology.IsBounded Q)
    (h : ∀ t : ℝ, 0 < t → ∀ y : Fin d → ℝ, shiftCount P t y = shiftCount Q t y) : P ⊆ Q := by sorry
