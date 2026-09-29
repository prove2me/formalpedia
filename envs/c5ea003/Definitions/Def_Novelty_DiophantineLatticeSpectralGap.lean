-- Prove2me | Definitions.Def_Novelty_DiophantineLatticeSpectralGap
-- name    : Novelty_DiophantineLatticeSpectralGap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:14:02.578848+00:00
-- url     : https://prove2.me/theorems/68a04c73-1c67-4ec3-9fe6-2d1f88cdeedc
-- title:
--   Aether Catalog definitions — Novelty_DiophantineLatticeSpectralGap
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.DiophantineLatticeSpectralGap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/DiophantineLatticeSpectralGap.lean by skeleton subtraction
import Mathlib

/-!
# Spectral bounds for non-homogeneous integral quadratic forms

Let `B` be a symmetric rational matrix which is **positive definite over `ℚ`**, and let
`Q(x) = xᵀBx` be the associated quadratic form on the lattice `L = ℤⁿ ⊆ ℚⁿ`.  A
*non-homogeneous* form is `F(x) = Q(x - t)` for a fixed rational shift `t`; the integral
solutions of `F(x) = c` are the lattice points on a `Q`-sphere around `t`.  The basic
quantitative invariants are

* the **minimal lattice energy** (homogeneous minimum) `λ₁ = min_{m ≠ 0} Q(m)`, and
* the **spectral gap** (inhomogeneous minimum) `μ(t) = min_{m ∈ L} Q(t - m)`, the smallest
  value the non-homogeneous form attains — equivalently the largest `c` such that
  `F(x) = c'` has *no* integral solution for all `c' < c`.

## Main results

* `half_shortest_inhomMin_ge` : if `v` realises `λ₁` then `Q(v/2 - m) ≥ λ₁/4` for **every**
  lattice point `m`.  This is the sharp form of the mission's `SpectralGap ≥ MinLatticeEnergy`:
  the factor `1/4` is forced (see `standard_form_gap_quarter`).
* `half_shortest_isInhomMin` : the bound is an equality, `μ(v/2) = λ₁/4`, for every
  positive-definite form in every dimension.
* `no_integral_solution_below_gap` : the Diophantine reading — for `0 ≤ c < λ₁/4` the
  non-homogeneous equation `Q(x - v/2) = c` has no integral solution; equivalently the
  integral equation `Q(w) = 4c` has no solution `w ≡ v (mod 2L)`.
* `covering_ge_quarter_min` : the packing–covering inequality `μ(Q) ≥ λ₁/4` for the
  covering radius.
* `diagonal_isMinEnergy`, `diagonal_covering_le` : for a diagonal form `Σ aᵢxᵢ²` the minimal
  lattice energy is `min aᵢ` while the covering radius² is at most `(Σ aᵢ)/4`, so the ratio
  `μ/λ₁` is unbounded: the deep hole `v/2` is far from being a deepest hole.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the mission stub `SpectralGap Q c ≥ MinLatticeEnergy Q` is
dimensionally wrong; the correct universal statement should carry a factor coming from the
`2`-torsion of `L/2L`, i.e. `μ ≥ λ₁/4`.
Experiment (Experimenter): exact rational enumeration over positive-definite binary forms
`(a,b,c) ∈ {(1,0,1),(1,1,1),(2,1,3),(1,0,5),(3,2,7),(5,4,9)}` gave `μ(v/2) − λ₁/4 = 0` in
*every* case (see `ComputationalEvidence.md`), never `μ ≥ λ₁`.  So the stub is false and the
`1/4`-version is not merely true but *sharp*.
Analysis (Analyst): the mechanism is parity: `Q(v/2 − m) = Q(v − 2m)/4` and `v − 2m` can
never vanish, because `v = 2m` would exhibit the lattice vector `m ≠ 0` of energy `λ₁/4`.
Only `λ₁ > 0` and minimality are used — no reduction theory, no positivity of `B` beyond
`Q(v) > 0`.  Equality then comes for free from `m = 0`.
Critique (Critic): the hypotheses are non-vacuous (`standard_isMinEnergy` witnesses them for
`ℤⁿ`), the conclusion is not definitional, and the constant is optimal.  We were careful that
`half_shortest_inhomMin_ge` does *not* assume `t` is a deepest hole: for `ℤⁿ` with `n ≥ 2`
the true covering radius² is `n/4 > 1/4`, so the theorem is a lower bound of a different
nature than the covering radius (`standard_covering_le`, `deepHole_isInhomMin`).
Synthesis (PI): `μ(v/2) = λ₁/4` is an exact identity valid for all positive-definite
rational forms; the covering radius is bounded below by it and, in the diagonal case, can
exceed it by an arbitrarily large factor.
-/

namespace DiophantineLattice

open Finset

variable {n : ℕ}

/-! ## The form and its bilinear companion -/

/-- The symmetric bilinear form attached to a rational matrix. -/
def bil (B : Matrix (Fin n) (Fin n) ℚ) (x y : Fin n → ℚ) : ℚ :=
  ∑ i, ∑ j, B i j * x i * y j

/-- The quadratic form `Q(x) = xᵀ B x`. -/
def form (B : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ := bil B x x

/-- The embedding of the lattice `ℤⁿ` into `ℚⁿ`. -/
def emb (m : Fin n → ℤ) : Fin n → ℚ := fun i => (m i : ℚ)




/-- `Q` is positive definite over `ℚ`. -/
def PosDef (B : Matrix (Fin n) (Fin n) ℚ) : Prop := ∀ x : Fin n → ℚ, x ≠ 0 → 0 < form B x

/-! ## Lattice invariants -/

/-- `lam` is the **minimal lattice energy** of `Q`: it is attained by some nonzero lattice
vector and no nonzero lattice vector has smaller energy. -/
def IsMinEnergy (B : Matrix (Fin n) (Fin n) ℚ) (lam : ℚ) : Prop :=
  (∃ v : Fin n → ℤ, v ≠ 0 ∧ form B (emb v) = lam) ∧
    ∀ m : Fin n → ℤ, m ≠ 0 → lam ≤ form B (emb m)

/-- `mu` is the **spectral gap** of the non-homogeneous form `x ↦ Q(x - t)`: the smallest
value it attains on the lattice. -/
def IsInhomMin (B : Matrix (Fin n) (Fin n) ℚ) (t : Fin n → ℚ) (mu : ℚ) : Prop :=
  (∃ m : Fin n → ℤ, form B (fun i => t i - emb m i) = mu) ∧
    ∀ m : Fin n → ℤ, mu ≤ form B (fun i => t i - emb m i)

/-- The half of a lattice vector, as the shift of a non-homogeneous form. -/
def halfPt (v : Fin n → ℤ) : Fin n → ℚ := fun i => (v i : ℚ) / 2

/-! ## The parity mechanism -/



/-! ## The sharp spectral gap at a half shortest vector -/






/-! ## Sharpness: the standard form on `ℤⁿ` -/




/-- The first standard basis vector, as an integer lattice point. -/
def e0 (hn : 0 < n) : Fin n → ℤ := fun i => if i = ⟨0, hn⟩ then 1 else 0




end DiophantineLattice


