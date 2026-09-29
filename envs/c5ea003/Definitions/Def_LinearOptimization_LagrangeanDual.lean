-- Prove2me | Definitions.Def_LinearOptimization_LagrangeanDual
-- name    : LinearOptimization_LagrangeanDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-09T15:59:13.502647+00:00
-- url     : https://prove2.me/theorems/5afdc149-4197-4710-be93-f3fd5ba8a9f2
-- title:
--   Lagrangean dual of an integer program
-- statement:
--   **(Lagrangean dual of an integer program — Bertsimas & Tsitsiklis, Section 11.4, pp. 494–495.)** Consider the integer programming problem (11.5): minimize $c'x$ subject to $Ax \ge b$, $Dx \ge d$, $x$ integer, where $A$, $D$, $b$, $c$, $d$ have integer entries; let $Z_{IP}$ be its optimal cost and let $X = \{x\ \text{integer} \mid Dx \ge d\}$.
--
--   Let $p \ge 0$ be a vector of dual variables (Lagrange multipliers) of the same dimension as $b$, dualizing the constraints $Ax \ge b$. For a fixed vector $p$, $Z(p)$ is the optimal cost of the problem (11.6):
--
--   $$\text{minimize}\ c'x + p'(b - Ax) \quad \text{subject to}\ x \in X.$$
--
--   The *Lagrangean dual* is the problem (11.7):
--
--   $$\text{maximize}\ Z(p) \quad \text{subject to}\ p \ge 0,$$
--
--   with optimal value $Z_D = \max_{p \ge 0} Z(p)$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Section 11.4, problems (11.6)-(11.7), pp. 494-495

import Definitions.Def_LinearOptimization_IntegerProgram

/-!
The Lagrangean dual objective and the Lagrangean dual value.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997:

- **§4.10 (p. 184), Eq. (4.7).** For the primal `min c'x` subject to
  `Ax ≥ b`, `x ∈ P` (with `P = {x | Dx ≥ d}`), the dual objective is
  `g(p) = min_{x ∈ P} [c'x + p'(b − Ax)]`, and the dual problem is
  `max g(p)` subject to `p ≥ 0`.
- **§11.4 (pp. 494–495), problems (11.6)–(11.7).** For the integer
  program (11.5) with `X = {x integer | Dx ≥ d}`, the constraints
  `Ax ≥ b` are dualized with multipliers `p ≥ 0`:
  `Z(p) = min_{x ∈ X} (c'x + p'(b − Ax))` (problem 11.6) and the
  Lagrangean dual is `Z_D = max_{p ≥ 0} Z(p)` (problem 11.7).

Both use the IDENTICAL sign convention (penalty ADDED as `p'(b − Ax)` for
dualized `Ax ≥ b`, `p ≥ 0` — pinned verbatim from the source), so ONE
inner-minimization def `lagrangeanObjective`, parametrized by the ground
set `S`, serves both: `S = polyhedron D d` gives §4.10's `g(p)`, and
`S = lagrangeanIntegerSet D d` gives §11.4's `Z(p)` (reusability-first).
Values are `EReal`: `Z(p) = ⊥` when the inner minimization is unbounded
below, `⊤` when `S = ∅`; `Z_D` is the `EReal` supremum over `p ≥ 0`
(the book's "max") — never an ℝ-valued `sInf` with junk.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, §11.4 (p. 494).** The tractable ground set
`X = {x integer | Dx ≥ d}` over which the Lagrangean relaxation
minimizes. -/
def lagrangeanIntegerSet {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ)
    (d : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ polyhedron D d ∧ IsIntegerPoint x}

/-- **Bertsimas & Tsitsiklis, Eq. (4.7) (p. 184) / problem (11.6) (p. 494).** The Lagrangean
dual objective over the ground set `S`:
`g(p) = Z(p) = inf_{x ∈ S} (c'x + p'(b − Ax))`, `EReal`-valued
(`⊥` = inner minimization unbounded below, `⊤` = `S` empty). -/
noncomputable def lagrangeanObjective {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (S : Set (Fin n → ℝ)) (p : Fin m → ℝ) : EReal :=
  ⨅ x ∈ S, ((c ⬝ᵥ x + p ⬝ᵥ (b - A.mulVec x) : ℝ) : EReal)

/-- **Bertsimas & Tsitsiklis, problem (11.7) (p. 495) / §4.10 dual problem (p. 184).** The
Lagrangean dual value `Z_D = sup_{p ≥ 0} Z(p)` (`EReal` supremum — the
book's "max"). -/
noncomputable def lagrangeanDualValue {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (S : Set (Fin n → ℝ)) : EReal :=
  ⨆ p ∈ {p : Fin m → ℝ | 0 ≤ p}, lagrangeanObjective A b c S p

end LinearOptimization


