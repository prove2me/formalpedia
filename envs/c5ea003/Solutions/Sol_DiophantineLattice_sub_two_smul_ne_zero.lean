-- Prove2me | solution 1 for DiophantineLattice.sub_two_smul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:58:09.9596+00:00
-- url     : https://prove2.me/submissions/00e2bc41-8ebf-4897-8d48-67e48db63e02

-- Sol generated from Novelty/DiophantineLatticeSpectralGap.lean
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap
import Theorems.Thm_DiophantineLattice_form_smul

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

open DiophantineLattice

open Finset

variable {n : ℕ}

/-! ## The form and its bilinear companion -/








/-! ## Lattice invariants -/




/-! ## The parity mechanism -/



/-! ## The sharp spectral gap at a half shortest vector -/






/-! ## Sharpness: the standard form on `ℤⁿ` -/









open DiophantineLattice in
theorem solution{B : Matrix (Fin n) (Fin n) ℚ} {lam : ℚ} (hpos : 0 < lam)
    (hmin : ∀ m : Fin n → ℤ, m ≠ 0 → lam ≤ form B (emb m))
    {v : Fin n → ℤ} (hv : form B (emb v) = lam) (m : Fin n → ℤ) :
    (fun i => v i - 2 * m i) ≠ 0 := by
  intro h
  have hvm : ∀ i, v i = 2 * m i := by
    intro i
    have : (fun i => v i - 2 * m i) i = (0 : Fin n → ℤ) i := by rw [h]
    simpa [sub_eq_zero] using this
  have hm0 : m ≠ 0 := by
    intro hm
    have hv0 : v = 0 := by
      funext i; rw [hvm i, hm]; simp
    rw [hv0] at hv
    have hz : form B (emb (0 : Fin n → ℤ)) = 0 := by
      simp [form, bil, emb]
    rw [hz] at hv
    linarith
  have hemb : emb v = fun i => (2 : ℚ) * (emb m) i := by
    funext i
    show ((v i : ℚ)) = 2 * (m i : ℚ)
    rw [hvm i]; push_cast; ring
  have h4 : lam = 4 * form B (emb m) := by
    rw [← hv, hemb, form_smul]; ring
  have := hmin m hm0
  linarith
