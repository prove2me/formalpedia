-- Prove2me | Definitions.Def_LinearOptimization_EllipsoidMethod
-- name    : LinearOptimization_EllipsoidMethod
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-06T14:42:17.78152+00:00
-- url     : https://prove2.me/theorems/a46b06ca-f3c1-463d-9e16-6c1c7a0cdfff
-- title:
--   The ellipsoid method
-- statement:
--   **(The ellipsoid method, boxed algorithm, p. 371, as an iteration predicate)**
--
--   Input:
--
--   - **(a)** a matrix $A$ and a vector $\mathbf{b}$ defining $P = \{\mathbf{x} \in \mathbb{R}^n \mid \mathbf{a}_i'\mathbf{x} \ge b_i,\ i = 1, \dots, m\}$;
--   - **(b)** a number $v$ such that either $P$ is empty or $\mathrm{Vol}(P) > v$;
--   - **(c)** a ball $E_0 = E(\mathbf{x}_0, r^2 I)$ with volume at most $V$, such that $P \subset E_0$.
--
--   Initialization: $t^* = \lceil 2(n+1)\log(V/v) \rceil$; $D_0 = r^2 I$; $t = 0$.
--
--   Main iteration:
--
--   - **(a)** if $t = t^*$ stop, $P$ is empty;
--   - **(b)** if $\mathbf{x}_t \in P$ stop, $P$ is nonempty;
--   - **(c)** if $\mathbf{x}_t \notin P$ find a violated constraint, i.e., an $i$ with $\mathbf{a}_i'\mathbf{x}_t < b_i$;
--   - **(d)** let $H_t = \{\mathbf{x} \mid \mathbf{a}_i'\mathbf{x} \ge \mathbf{a}_i'\mathbf{x}_t\}$ and let $E_{t+1} = E(\mathbf{x}_{t+1}, D_{t+1}) \supset E_t \cap H_t$ be given by the Theorem 8.1 update
--
--     $$\mathbf{x}_{t+1} = \mathbf{x}_t + \frac{1}{n+1}\frac{D_t\mathbf{a}_i}{\sqrt{\mathbf{a}_i'D_t\mathbf{a}_i}}, \qquad D_{t+1} = \frac{n^2}{n^2-1}\Big(D_t - \frac{2}{n+1}\frac{D_t\mathbf{a}_i\mathbf{a}_i'D_t}{\mathbf{a}_i'D_t\mathbf{a}_i}\Big);$$
--
--   - **(e)** $t := t+1$.
--
--   *Encoding:* Encoded as a predicate on sequences $(\mathbf{x}_t, D_t)$: a step is admissible at $t$ iff $\mathbf{x}_t \notin P$ and there exists a violated row $i$ producing $(\mathbf{x}_{t+1}, D_{t+1})$ by the update above — covering every rule for choosing the violated constraint.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, ellipsoid method box, p. 371

import Mathlib.Data.Real.Sqrt
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_Polyhedron

/-!
The ellipsoid method as an iteration predicate.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, Chapter 8 — the boxed algorithm on p. 371, whose
update step is the Theorem 8.1 (p. 366) construction: given the current
ellipsoid `E(z, D)` and a nonzero vector `a`,

- new center `z̄ = z + (1/(n+1)) · Da / √(a'Da)`,
- new matrix `D̄ = (n²/(n²−1)) · (D − (2/(n+1)) · Daa'D / (a'Da))`.

The algorithm (p. 371): given `P = {x | aᵢ'x ≥ bᵢ, i = 1, …, m}`, at
iteration `t` with current ellipsoid `E(x_t, D_t)`, if `x_t ∉ P` pick a
violated constraint `aᵢ'x_t < bᵢ` and produce `E(x_{t+1}, D_{t+1})` by the
update above with `a = aᵢ` (the halfspace `H_t = {x | aᵢ'x ≥ aᵢ'x_t}`
retains all of `P ∩ E_t`); if `x_t ∈ P` stop ("P is nonempty"); after `t*`
iterations stop ("P is empty").

Design (series architecture decision — algorithms are predicates, not
programs): `IsEllipsoidStep` relates `(x_t, D_t)` to `(x_{t+1}, D_{t+1})`
through SOME violated row, and `IsEllipsoidRun` requires an admissible
step at every `t < T` at which the current center is infeasible — so the
correctness theorem (Theorem 8.2) quantifies over every admissible run and
every rule for choosing the violated constraint. Positive definiteness of
`D_t` propagates by Theorem 8.1; the `√·` and the scalar inverses are
Lean-total (junk values only arise outside the guarded statements). The
factor `n²/(n²−1)` forces the `2 ≤ n` hypothesis carried by the theorems.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Theorem 8.1 / algorithm step (d) (pp. 366, 371).** The updated
center `z̄ = z + (1/(n+1)) · Da / √(a'Da)`. -/
noncomputable def ellipsoidUpdateCenter {n : ℕ} (z : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : Fin n → ℝ :=
  z + ((1 : ℝ) / (n + 1)) • (Real.sqrt (a ⬝ᵥ D.mulVec a))⁻¹ • D.mulVec a

/-- **Bertsimas & Tsitsiklis, Theorem 8.1 / algorithm step (d) (pp. 366, 371).** The updated
matrix `D̄ = (n²/(n²−1)) · (D − (2/(n+1)) · Daa'D / (a'Da))`; `Daa'D` is
the matrix product `D * (aa') * D` with `aa' = vecMulVec a a`. -/
noncomputable def ellipsoidUpdateMatrix {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (D - ((2 : ℝ) / (n + 1)) • (a ⬝ᵥ D.mulVec a)⁻¹ •
      (D * vecMulVec a a * D))

/-- **Bertsimas & Tsitsiklis, p. 371, main iteration steps (c)–(d).** One admissible step of
the ellipsoid method for `P = {x | Ax ≥ b}`: SOME violated constraint
`aᵢ'x < bᵢ` is found, and the next center/matrix are produced by the
Theorem 8.1 update with `a = aᵢ` — covering every rule for choosing the
violated constraint. -/
def IsEllipsoidStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (x' : Fin n → ℝ) (D' : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ i : Fin m, A i ⬝ᵥ x < b i ∧
    x' = ellipsoidUpdateCenter x D (A i) ∧
    D' = ellipsoidUpdateMatrix D (A i)

/-- **Bertsimas & Tsitsiklis, p. 371 (the boxed algorithm as a run predicate).** The sequences
`(x_t, D_t)` form an admissible run of the ellipsoid method on
`P = {x | Ax ≥ b}` up to time `T`: at every `t < T` whose center is
infeasible, the next iterate is produced by an admissible step (steps
(c)–(d)); once some `x_t ∈ P` the algorithm has stopped ("P is nonempty")
and the run is unconstrained afterwards. -/
def IsEllipsoidRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : ℕ → Fin n → ℝ)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (T : ℕ) : Prop :=
  ∀ t < T, x t ∉ polyhedron A b →
    IsEllipsoidStep A b (x t) (D t) (x (t + 1)) (D (t + 1))

end LinearOptimization


