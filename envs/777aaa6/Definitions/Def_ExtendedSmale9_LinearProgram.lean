-- Prove2me | Definitions.Def_ExtendedSmale9_LinearProgram
-- name    : ExtendedSmale9_LinearProgram
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T14:03:10.920576+00:00
-- url     : https://prove2.me/theorems/d6c80aa3-5990-4176-9452-6407c8ddd406
-- title:
--   Linear programming (1.1), LP inputs, and the matrices $A(\alpha,\beta,m,N)$ of (11.1)
-- statement:
--   An LP input is $\iota=(y,A)\in\mathbb R^m\times\mathbb R^{m\times N}$. Its evaluations are the entries $y_i$ and $A_{ij}$.
--
--   The feasible set is $\{x\in\mathbb R^N: Ax=y,\ x\ge0\}$, and the solution set of (1.1) is $\operatorname{argmin}\{\langle x,c\rangle : Ax=y,\ x\ge0\}$. The LP solution map uses $c=\mathbf 1_N$ and takes values in $M_N=(\mathbb R^N,\|\cdot\|_p)$.
--
--   For (11.1),
--   $$A(\alpha,\beta,m,N) = \begin{pmatrix} (\alpha\ \ \beta\ \ {-1}) \oplus I_{m-1} & 0\end{pmatrix},\qquad y^A(y_1,m)=y_1e_1 .$$
--   That is, the first row of $A(\alpha,\beta,m,N)$ is $(\alpha,\beta,-1,0,\dots,0)$ and row $i\ge2$ is $e_{i+2}^\top$.
-- source:
--   A. Bastounis, A. C. Hansen, V. Vlačić, *The extended Smale's 9th problem — On computational barriers and paradoxes in estimation, regularisation, computer-assisted proofs, and learning* (preprint, 126 pp., version of 28 Jan 2021), §1.1 problem (1.1) (p. 4), (9.13) (p. 29), §11.1 display (11.1) (p. 45).

import Mathlib

/-!
# Linear programming (1.1) and the inputs of §11.1

Bastounis–Hansen–Vlačić, *The extended Smale's 9th problem*:
* problem (1.1): `z ∈ argmin_x ⟨x, c⟩` subject to `Ax = y`, `x ≥ 0`;
* the input sets `Ω_{m,N} ⊆ ℝ^m × ℝ^{m×N}` of (9.13), with evaluations the entries of
  `y` and `A`, and `c = (1, …, 1)`;
* the output space `M_N = ℝ^N` with the `‖·‖_p` norm;
* the matrices `A(α, β, m, N)` and vectors `y^A(y₁, m)` of (11.1).
-/

open scoped ENNReal

namespace ExtendedSmale9

/-- An LP input `ι = (y, A) ∈ ℝ^m × ℝ^{m×N}`. -/
abbrev LPInput (m N : ℕ) : Type := (Fin m → ℝ) × Matrix (Fin m) (Fin N) ℝ

/-- The evaluation family on LP inputs: the coordinates `y_i` and entries `A_{ij}`
(regarded as complex numbers). -/
noncomputable def lpEval {m N : ℕ} : Fin m ⊕ (Fin m × Fin N) → LPInput m N → ℂ
  | Sum.inl i, ι => (ι.1 i : ℂ)
  | Sum.inr ij, ι => (ι.2 ij.1 ij.2 : ℂ)

/-- The feasible set `{x ∈ ℝ^N | Ax = y, x ≥ 0}` of (1.1). -/
def lpFeasible {m N : ℕ} (y : Fin m → ℝ) (A : Matrix (Fin m) (Fin N) ℝ) : Set (Fin N → ℝ) :=
  {x | A.mulVec x = y ∧ ∀ i, 0 ≤ x i}

/-- The solution set of (1.1): `argmin_x ⟨x, c⟩` subject to `Ax = y`, `x ≥ 0`. -/
def lpArgmin {m N : ℕ} (c : Fin N → ℝ) (y : Fin m → ℝ) (A : Matrix (Fin m) (Fin N) ℝ) :
    Set (Fin N → ℝ) :=
  {z | z ∈ lpFeasible y A ∧ ∀ x ∈ lpFeasible y A, c ⬝ᵥ z ≤ c ⬝ᵥ x}

/-- The LP solution map `Ξ(y, A)` with `c = 1_N = (1, …, 1)`, as a subset of
`M_N = (ℝ^N, ‖·‖_p)`. -/
def lpSolution {m N : ℕ} (p : ℝ≥0∞) (ι : LPInput m N) :
    Set (PiLp p (fun _ : Fin N => ℝ)) :=
  WithLp.toLp p '' lpArgmin (fun _ => 1) ι.1 ι.2

/-- The matrix `A(α, β, m, N) = ((α β −1) ⊕ I_{m−1}   0)` of (11.1): its first row is
`(α, β, −1, 0, …, 0)` and, for `2 ≤ i ≤ m`, its `i`-th row is the standard basis row
`e_{i+2}` (zero-based: row `i ≥ 1` has a single `1` in column `i + 2`); all other entries
vanish. -/
def lpMatrixA (α β : ℝ) (m N : ℕ) : Matrix (Fin m) (Fin N) ℝ := fun i j =>
  if (i : ℕ) = 0 then
    (if (j : ℕ) = 0 then α else if (j : ℕ) = 1 then β else if (j : ℕ) = 2 then -1 else 0)
  else if (j : ℕ) = (i : ℕ) + 2 then 1 else 0

/-- The vector `y^A(y₁, m) = y₁ e₁ ∈ ℝ^m` of (11.1). -/
def lpVectorA (y₁ : ℝ) (m : ℕ) : Fin m → ℝ := fun i => if (i : ℕ) = 0 then y₁ else 0

end ExtendedSmale9


