-- Prove2me | Definitions.Def_MCNoSpuriousMinModel
-- name    : MCNoSpuriousMinModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-04T14:11:18.269633+00:00
-- url     : https://prove2.me/theorems/ef50175b-1e61-4fca-942b-4fc571eddd4e
-- title:
--   Model layer: objective, optimality conditions, auxiliary function $K$, and the good-sample predicate
-- statement:
--   This definition file sets up the framework for the mission. The ground truth is a rank-$r$ positive semidefinite matrix $M = ZZ^\top$ with $Z\in\mathbb{R}^{d\times r}$ $\mu$-incoherent, observed on a symmetric set $\Omega$ of entries.
--
--   **From Ge–Lee–Ma 2016** (the paper whose theorem this mission proves): the entry-restriction operator $P_\Omega$; the row incoherence condition $\|Z_i\|\le\mu/\sqrt d\,\|Z\|_F$ (Assumption 1); the row regularizer $R(X)=\sum_i(\|X_i\|-\alpha)_+^4$ with its explicit gradient $\nabla R(X)=\Gamma X$ and Hessian quadratic form; the regularized objective
--
--   $$f(X)=\tfrac12\|P_\Omega(ZZ^\top-XX^\top)\|_F^2+\lambda R(X),$$
--
--   its gradient, and the first- and second-order optimality conditions (their eqs. (5.2)–(5.3)).
--
--   **From Ge–Jin–Zheng 2017 / Jin et al. 2017**: the Hessian quadratic form $\langle V,\nabla^2 f(X)[V]\rangle$ and the auxiliary function $K(X)=\langle\Delta,\nabla^2 f(X)[\Delta]\rangle-4\langle\nabla f(X),\Delta\rangle$ along an error direction $\Delta = X-U$.
--
--   **From Chen–Li 2019**: the sample indicator matrix and the centered deviation norm $\|\Omega-tJ\|$ (the single scalar through which randomness enters); the sampling-deviation functional $D_{\Omega,t}(A,B)=\langle P_\Omega A,P_\Omega B\rangle-t\langle A,B\rangle$ (their eq. (4.2)); the column-span projection used for the tangent space; the sampling regime of their Corollary 2.2; and the good-sample predicate whose two nontrivial fields are exactly the conclusions of their Lemmas 4.1 (spectral bound on $\|\Omega-pJ\|$, after Bandeira–van Handel and Vu) and 4.2 (tangent-space concentration, after Candès–Recht, Recht, and Gross).
--
--   **Formalization Note** All constants are explicit: the $[100,200]$ tuning windows are Chen–Li's own; the $10^{10}$ in the sampling condition is a generous stand-in for their unspecified absolute constant $C$; the incoherence parameter is Ge–Lee–Ma's row version rather than the Candès–Recht eigenspace version used by Chen–Li, and the sampling polynomial is stated accordingly. In the regularizer gradient the exponent is $3$ (the derivative of $(t-\alpha)_+^4$), where Ge–Lee–Ma's Proposition 5.2 prints a typographical $4$. Lean's total-function conventions ($0/0=0$, junk values for empty suprema) make all formulas total. The probabilistic layer (a Bernoulli-$p$ sample is good w.h.p., Chen–Li Lemmas 4.1–4.2) is out of scope of this mission and is a natural follow-up mission.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], Sections 1-2 and 4 (objective eq. (1.1), tuning windows of Theorem 2.1, deviation functional eq. (4.2), good-sample facts Lemmas 4.1-4.2, sampling regime Corollary 2.2). Provenance: objective, regularizer and incoherence from Ge, Lee, Ma 2016, Matrix Completion has No Spurious Local Minimum, https://arxiv.org/abs/1605.07272 (v4), Assumption 1 and eq. (5.1); auxiliary function K from Ge, Jin, Zheng 2017, No Spurious Local Minima in Nonconvex Low Rank Problems, https://arxiv.org/abs/1704.00708, Section 4.

/-
Model layer for the mission "Matrix Completion has No Spurious Local Minimum".

The objective and regularizer are those of Ge–Lee–Ma 2016 (arXiv:1605.07272v4,
eq. (5.1)): M = Z Zᵀ with Z ∈ ℝ^{d×r} μ-incoherent (Assumption 1), observations P_Ω
for a symmetric sample set Ω, and
  f(X) = ½‖P_Ω(M − XXᵀ)‖_F² + λ R(X),   R(X) = Σᵢ (‖Xᵢ‖ − α)₊⁴.

The proof route formalized by this mission is the simplified one of
Ge–Jin–Zheng 2017 (arXiv:1704.00708) as executed by Chen–Li 2019 (arXiv:1711.01742v3):
the auxiliary function K(X) = ⟨Δ, ∇²f(X)[Δ]⟩ − 4⟨∇f(X), Δ⟩ along the aligned error
direction Δ = X − U, the sampling-deviation functional D_{Ω,p} (Chen–Li eq. (4.2)),
and the centered sampling matrix Ω − pJ whose spectral norm is the single quantity
through which randomness enters.

`GoodSample` states, as deterministic hypotheses on Ω, the two facts Chen–Li prove
hold with high probability (their Lemmas 4.1 and 4.2, after Bandeira–van Handel/Vu
and Candès–Recht/Recht), plus the sampling model's symmetry and a per-row count bound.
The probabilistic layer (ℙ[GoodSample] ≥ 1 − O(n⁻³)) is out of scope of this mission.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace MatrixCompletion.NoSpuriousMin

open Matrix

/-- Euclidean norm of a finite real vector. -/
noncomputable def vecNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ j, v j ^ 2)

/-- Trace (Frobenius) inner product ⟨A, B⟩ = tr(AᵀB) = Σᵢⱼ Aᵢⱼ Bᵢⱼ. -/
def innerM {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- Squared Frobenius norm ‖A‖_F². -/
def frobSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Frobenius norm ‖A‖_F. -/
noncomputable def frobNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (frobSq A)

/-- Euclidean norm of the i-th row of A. -/
noncomputable def rowNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : ℝ :=
  vecNorm (A i)

/-- The 2→∞ norm: the largest row norm, ‖A‖_{2→∞} = maxᵢ ‖Aᵢ‖. -/
noncomputable def twoInftyNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨆ i, rowNorm A i

/-- Largest singular value, via the variational characterization
σ_max(A) = sup { ‖Av‖ : ‖v‖ = 1 }. -/
noncomputable def sigmaMax {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨆ v : {v : Fin n → ℝ // vecNorm v = 1}, vecNorm (A.mulVec v.1)

/-- Smallest singular value of a (tall) matrix, via the variational characterization
σ_min(A) = inf { ‖Av‖ : ‖v‖ = 1 } (the r-th singular value when A is d×r, d ≥ r). -/
noncomputable def sigmaMin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨅ v : {v : Fin n → ℝ // vecNorm v = 1}, vecNorm (A.mulVec v.1)

/-- Restriction to the observed entries: P_Ω(A) agrees with A on Ω and is 0 outside. -/
def projSet {d : ℕ} (Ω : Finset (Fin d × Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => if (i, j) ∈ Ω then A i j else 0

/-- Assumption 1 of Ge–Lee–Ma (p. 2): every row of Z satisfies ‖Zᵢ‖ ≤ μ/√d · ‖Z‖_F. -/
def Incoherent {d r : ℕ} (μ : ℝ) (Z : Matrix (Fin d) (Fin r) ℝ) : Prop :=
  ∀ i, rowNorm Z i ≤ μ / Real.sqrt d * frobNorm Z

/-- The 0/1 indicator matrix of the sample set Ω. -/
def sampMatrix {d : ℕ} (Ω : Finset (Fin d × Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => if (i, j) ∈ Ω then 1 else 0

/-- The centered sampling deviation norm ‖Ω − tJ‖ (Chen–Li): the operator 2-norm of the
sample indicator matrix minus t times the all-ones matrix J.  This single scalar is the
only quantity through which the randomness of Ω enters the Chen–Li proof. -/
noncomputable def sampDevNorm {d : ℕ} (Ω : Finset (Fin d × Fin d)) (t : ℝ) : ℝ :=
  sigmaMax (sampMatrix Ω - t • Matrix.of fun _ _ => (1 : ℝ))

/-- The sampling-deviation functional D_{Ω,t}(A, B) = ⟨P_Ω A, P_Ω B⟩ − t⟨A, B⟩
(Chen–Li, eq. (4.2)). -/
def sampDev {d : ℕ} (Ω : Finset (Fin d × Fin d)) (t : ℝ)
    (A B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  innerM (projSet Ω A) (projSet Ω B) - t * innerM A B

/-- Orthogonal projection onto the column span of Z (for Z of full column rank):
P = Z (ZᵀZ)⁻¹ Zᵀ. -/
noncomputable def colProj {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Z * (Zᵀ * Z)⁻¹ * Zᵀ

/-- The row penalty h(t) = (t − α)₊⁴ (the paper's (|t| − α)⁴ 𝕀_{t ≥ α} for t ≥ 0). -/
noncomputable def hinge (α t : ℝ) : ℝ := max (t - α) 0 ^ 4

/-- The regularizer R(X) = Σᵢ (‖Xᵢ‖ − α)₊⁴ (eq. (5.1) with r(t) = (|t| − α)⁴ 𝕀_{t≥α}). -/
noncomputable def reg {d r : ℕ} (α : ℝ) (X : Matrix (Fin d) (Fin r) ℝ) : ℝ :=
  ∑ i, hinge α (rowNorm X i)

/-- The gradient ∇R(X) = Γ X of the regularizer (Proposition 5.2), where Γ is diagonal
with Γᵢᵢ = 4 (‖Xᵢ‖ − α)₊³ / ‖Xᵢ‖.  (The paper's Proposition 5.2 prints the exponent as 4;
the derivative of (t − α)₊⁴ is 4(t − α)₊³, which is the form its rank-1 counterpart on
p. 9 uses, so the cube is the intended reading.)  When ‖Xᵢ‖ < α the numerator vanishes,
and Lean's 0/0 = 0 convention makes the formula total. -/
noncomputable def regGrad {d r : ℕ} (α : ℝ) (X : Matrix (Fin d) (Fin r) ℝ) :
    Matrix (Fin d) (Fin r) ℝ :=
  Matrix.of fun i j => 4 * max (rowNorm X i - α) 0 ^ 3 / rowNorm X i * X i j

/-- Quadratic form V ↦ ⟨V, ∇²R(X)[V]⟩ of the regularizer's Hessian.  Row-wise, for the
radial function h(‖x‖) with h(t) = (t − α)₊⁴, the Hessian is
h''(t)·uuᵀ + (h'(t)/t)·(I − uuᵀ) with t = ‖Xᵢ‖, u = Xᵢ/t, h'(t) = 4(t−α)₊³,
h''(t) = 12(t−α)₊². -/
noncomputable def regHessQF {d r : ℕ} (α : ℝ) (X V : Matrix (Fin d) (Fin r) ℝ) : ℝ :=
  ∑ i,
    (12 * max (rowNorm X i - α) 0 ^ 2 * ((∑ j, X i j * V i j) / rowNorm X i) ^ 2
      + 4 * max (rowNorm X i - α) 0 ^ 3 / rowNorm X i
          * (vecNorm (V i) ^ 2 - ((∑ j, X i j * V i j) / rowNorm X i) ^ 2))

/-- The regularized objective (5.1): f(X) = ½‖P_Ω(ZZᵀ − XXᵀ)‖_F² + λ R(X). -/
noncomputable def objective {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ)
    (Ω : Finset (Fin d × Fin d)) (lam α : ℝ) (X : Matrix (Fin d) (Fin r) ℝ) : ℝ :=
  frobSq (projSet Ω (Z * Zᵀ - X * Xᵀ)) / 2 + lam * reg α X

/-- The gradient of the objective: ∇f(X) = 2 P_Ω(XXᵀ − ZZᵀ) X + λ ∇R(X). -/
noncomputable def objGrad {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ)
    (Ω : Finset (Fin d × Fin d)) (lam α : ℝ) (X : Matrix (Fin d) (Fin r) ℝ) :
    Matrix (Fin d) (Fin r) ℝ :=
  (2 : ℝ) • (projSet Ω (X * Xᵀ - Z * Zᵀ) * X) + lam • regGrad α X

/-- The first-order optimality condition (5.2): ∇f(X) = 0, i.e.
2 P_Ω(ZZᵀ) X = 2 P_Ω(XXᵀ) X + λ ∇R(X). -/
def FirstOrderPt {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (lam α : ℝ) (X : Matrix (Fin d) (Fin r) ℝ) : Prop :=
  objGrad Z Ω lam α X = 0

/-- The second-order optimality condition (5.3): for every direction V,
‖P_Ω(VXᵀ + XVᵀ)‖_F² + λ ⟨V, ∇²R(X)[V]⟩ ≥ 2 ⟨P_Ω(ZZᵀ − XXᵀ), VVᵀ⟩. -/
def SecondOrderPt {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (lam α : ℝ) (X : Matrix (Fin d) (Fin r) ℝ) : Prop :=
  ∀ V : Matrix (Fin d) (Fin r) ℝ,
    2 * innerM (projSet Ω (Z * Zᵀ - X * Xᵀ)) (V * Vᵀ) ≤
      frobSq (projSet Ω (V * Xᵀ + X * Vᵀ)) + lam * regHessQF α X V

/-- The quadratic form of the objective's Hessian at X in direction V:
⟨V, ∇²f(X)[V]⟩ = ‖P_Ω(VXᵀ + XVᵀ)‖_F² − 2⟨P_Ω(ZZᵀ − XXᵀ), VVᵀ⟩ + λ⟨V, ∇²R(X)[V]⟩.
`SecondOrderPt` is equivalent to this form being nonnegative in every direction. -/
noncomputable def hessQF {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ)
    (Ω : Finset (Fin d × Fin d)) (lam α : ℝ) (X V : Matrix (Fin d) (Fin r) ℝ) : ℝ :=
  frobSq (projSet Ω (V * Xᵀ + X * Vᵀ))
    - 2 * innerM (projSet Ω (Z * Zᵀ - X * Xᵀ)) (V * Vᵀ)
    + lam * regHessQF α X V

/-- The auxiliary function of Jin et al. 2017 / Ge–Jin–Zheng 2017, as used by Chen–Li:
K(X) = ⟨Δ, ∇²f(X)[Δ]⟩ − 4⟨∇f(X), Δ⟩ with Δ = X − U.  At any local minimum,
K(X) ≥ 0 for every U, by the first- and second-order optimality conditions. -/
noncomputable def Kfun {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ)
    (Ω : Finset (Fin d × Fin d)) (lam α : ℝ) (X U : Matrix (Fin d) (Fin r) ℝ) : ℝ :=
  hessQF Z Ω lam α X (X - U) - 4 * innerM (objGrad Z Ω lam α X) (X - U)

/-- The sampling-rate regime of Chen–Li's Corollary 2.2, expressed in Ge–Lee–Ma's
row-incoherence parameter μ.  The explicit constant 10¹⁰ is a stand-in for Chen–Li's
unspecified absolute constant C, chosen generously; the polynomial shape
max{μ²rκ²·log d, μ⁴r²κ⁴}/d is theirs. -/
def SampleCondition (d r : ℕ) (p μ κ : ℝ) : Prop :=
  10 ^ 10 * μ ^ 4 * κ ^ 4 * r ^ 2 * Real.log d / d ≤ p ∧ p ≤ 1

/-- A "good sample": the deterministic properties of the observation set Ω that Chen–Li
prove hold with high probability over the off-diagonal symmetric Bernoulli(p) model,
stated as hypotheses.

Field origins:
* `symm`, `row_card` — the symmetric sampling model and the per-row count |Sᵢ| ≤ 2pd
  (shared with Ge–Lee–Ma, p. 9 and Lemma 5.4).
* `spec_bound` — Chen–Li Lemma 4.1 (after Bandeira et al. 2016, Vu 2018):
  ‖Ω − pJ‖ ≤ C(√(dp) + √(log d)), with the explicit constant 100.
* `tangent_conc` — Chen–Li Lemma 4.2 (after Candès–Recht 2009, Recht 2011, Gross 2011):
  restricted to the tangent space T = {W symmetric | (I−P)W(I−P) = 0} of the column
  span of Z, the sampling operator concentrates at relative accuracy 10⁻³. -/
structure GoodSample {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ)
    (Ω : Finset (Fin d × Fin d)) (p : ℝ) : Prop where
  symm : ∀ i j : Fin d, (i, j) ∈ Ω ↔ (j, i) ∈ Ω
  row_card : ∀ i : Fin d,
    (((Ω.filter fun e => e.1 = i)).card : ℝ) ≤ 2 * p * d
  spec_bound : sampDevNorm Ω p ≤
    100 * (Real.sqrt (d * p) + Real.sqrt (Real.log d))
  tangent_conc : ∀ W W' : Matrix (Fin d) (Fin d) ℝ,
    W.IsSymm → W'.IsSymm →
    (1 - colProj Z) * W * (1 - colProj Z) = 0 →
    (1 - colProj Z) * W' * (1 - colProj Z) = 0 →
    |sampDev Ω p W W'| ≤ p / 1000 * frobNorm W * frobNorm W'

end MatrixCompletion.NoSpuriousMin


