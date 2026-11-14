-- Prove2me | Theorems.Thm_DetValuationMilestone_canonical_projected_minValue_growth
-- name    : DetValuationMilestone.canonical_projected_minValue_growth
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T01:59:13.283483+00:00
-- url     : https://prove2.me/theorems/b50d5373-2d2e-443b-9e4a-f169b5f41753
-- title:
--   Finite canonical minor valuations under row projection
-- statement:
--   Let $R$ be a commutative ring with an additive non-Archimedean valuation $\nu:R\to\mathbb R\cup\{+\infty\}$, with $\nu(u)=+\infty$ exactly when $u=0$. Thus $\nu(uv)=\nu(u)+\nu(v)$ and $\nu(u+v)\ge\min(\nu(u),\nu(v))$.
--
--   Let $k=n+1\ge1$, let $I$ be finite, and let $H$ have $k$ rows and columns $h_\ell$ indexed by $I$. Suppose a square matrix $A$ has columns $A_i=c_i h_{x_i}$ and determinant $D\ne0$. Let $e_0$ be the first coordinate vector, and put $D_i=\det(A[i\leftarrow e_0])$. Deleting the first row of $H$ gives $\widehat H$.
--
--   The following four quantities are finite real numbers:
--
--   $$
--   \delta=\nu(D),\qquad
--   \alpha=\min_{i<k}\nu(D_i c_i),\qquad
--   \mu=\min_{z\in I^k}\nu(\det H_z),\qquad
--   \widehat\mu=\min_{y\in I^n}\nu(\det\widehat H_y).
--   $$
--
--   Here $H_z$ and $\widehat H_y$ select ordered tuples of columns, with repetitions allowed; a zero determinant has valuation $+\infty$. These canonical minima satisfy
--
--   $$
--   \alpha-\delta\le\widehat\mu-\mu.
--   $$
--
--   This is an abstract projected-minor inequality. The single assumption $D\ne0$ supplies the nonzero witnesses needed to make all minima finite, including when $n=0$. It can be reused in valued linear algebra without a metric, work function, prescribed coefficient field, or invertibility operation.
-- source:
--   Original abstract division-free formulation derived from Cramer's vector identity (Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, Matrix.mulVec_cramer, LinearAlgebra/Matrix/Adjugate.lean, line 284: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/LinearAlgebra/Matrix/Adjugate.lean#L276-L285) and the explicitly stated non-Archimedean valuation axioms. Motivated by the algebraic inequality used in Coester–Koutsoupias–Zbysiński, The k-server conjecture is true, arXiv:2609.15979, Lemma 4.3; this result is the abstract inequality direction and does not assert the paper's extended-cost equality.

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
open scoped BigOperators

theorem DetValuationMilestone.canonical_projected_minValue_growth
    {n : ℕ} {R ι : Type*} [CommRing R] [Fintype ι]
    (ν : R → WithTop ℝ)
    (htop : ∀ x, ν x = ⊤ ↔ x = 0)
    (hmul : ∀ x y, ν (x * y) = ν x + ν y)
    (hadd : ∀ x y, min (ν x) (ν y) ≤ ν (x + y))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (H : Matrix (Fin (n + 1)) ι R)
    (x : Fin (n + 1) → ι) (c : Fin (n + 1) → R)
    (hcol : ∀ i, (fun r => A r i) = c i • (fun r => H r (x i)))
    (hdet : A.det ≠ 0) :
    ∃ δ α μ μhat : ℝ,
      ν A.det = (δ : WithTop ℝ) ∧
      (Finset.univ.inf fun i => ν ((A.updateCol i (Pi.single 0 1)).det * c i)) =
        (α : WithTop ℝ) ∧
      (Finset.univ.inf fun z : Fin (n + 1) → ι => ν (H.submatrix id z).det) =
        (μ : WithTop ℝ) ∧
      (Finset.univ.inf fun y : Fin n → ι => ν (H.submatrix Fin.succ y).det) =
        (μhat : WithTop ℝ) ∧
      α - δ ≤ μhat - μ := by sorry
