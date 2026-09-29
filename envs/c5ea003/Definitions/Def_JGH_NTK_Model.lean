-- Prove2me | Definitions.Def_JGH_NTK_Model
-- name    : JGH_NTK_Model
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-26T01:32:36.472151+00:00
-- url     : https://prove2.me/theorems/5f9bce55-efdd-4a15-b55c-3e441e4de8ee
-- title:
--   Finite Neural Networks, Gaussian Initialization, and the Limiting NTK
-- statement:
--   ### Mathematical model
--
--   ### Notation and probability model
--   Let $d,q\ge1$ be the input and output dimensions, $h\ge0$ the number of hidden
--   layers, $L=h+1$, $\beta>0$, and $\sigma:\mathbb R\to\mathbb R$ a Lipschitz
--   activation with a nonnegative Lipschitz constant $K$. For widths
--   $n_0=d$, $n_L=q$, and $n_\ell=w_{\ell-1}+1$ with $w_i\in\mathbb N$, the
--   probability space $\Omega_w$ is the finite real parameter space with every
--   weight and bias coordinate independently $\mathcal N(0,1)$. Its law is $\mathbb P_w$.
--   The network has the recursion
--   $$z^{(\ell+1)}_j(x)=\frac{1}{\sqrt{n_\ell}}\sum_i W^{(\ell)}_{ji}
--   a^{(\ell)}_i(x)+\beta b^{(\ell)}_j,\qquad
--    a^{(0)}(x)=x,\quad a^{(\ell)}(x)=\sigma(z^{(\ell)}(x))\ (1\le\ell\le h),$$
--   with output $f_\theta=z^{(L)}$. The full kernel, including all weights and biases, is
--   $$\Theta^{(L)}_{kk'}(\theta;x,y)=\sum_p
--   \partial_{\theta_p}f_{\theta,k}(x)\partial_{\theta_p}f_{\theta,k'}(y).$$
--   For a centered Gaussian pair $(U,V)$ with covariance induced by
--   $\Sigma^{(\ell)}$ on $(x,y)$, put
--   $$\Sigma^{(1)}(x,y)=\langle x,y\rangle/d+\beta^2,\qquad
--   \Sigma^{(\ell+1)}(x,y)=\mathbb E[\sigma(U)\sigma(V)]+\beta^2,$$
--   $$\dot\Sigma^{(\ell+1)}(x,y)=\mathbb E[\sigma'(U)\sigma'(V)],\qquad
--   \Theta_\infty^{(1)}=\Sigma^{(1)},\quad
--   \Theta_\infty^{(\ell+1)}=\Theta_\infty^{(\ell)}\dot\Sigma^{(\ell+1)}+\Sigma^{(\ell+1)}.$$
--   All kernel products in the last expression are pointwise. Local index $h$ in
--   `covarianceKernel` and `limitingNTK` denotes paper depth $h+1$.
--   The dataset $X=(x_i)_{i<N}$ is any fixed finite family; repetitions and $N=0$
--   are allowed. $\delta_{kk'}$ is the Kronecker delta.
--
--   The limit takes $n_1$ to infinity first and $n_h$ last. More precisely, for
--   any required error tolerance, the width condition is
--   $\forall^{\mathrm{eventually}}w_{h-1}\cdots
--   \forall^{\mathrm{eventually}}w_0$; each inner threshold may depend on the fixed
--   outer widths. For $h=0$ the filter is concentrated on the unique empty width
--   vector, so the statements require the exact affine base case. This is not a
--   simultaneous-width or whole-input-space uniform limit.
--
--   Formalization note: Gaussian measures are concrete Mathlib measures, including
--   singular covariance. The covariance-validity milestone establishes their
--   covariance interpretation; it is not a hypothesis of either convergence target.
--   The activation assumption is only Lipschitz. Derivatives take Mathlib's zero
--   value at points without derivatives, and proofs must justify the null exceptional
--   set under positive Gaussian bias. Native convergence in distribution includes
--   almost-everywhere measurability and weak convergence of probability laws.
--   Primary source conventions: Jacot–Gabriel–Hongler, Section 2, PDF pp. 2–3;
--   Section 4.1, PDF p. 5, Proposition 1, Theorem 1 and Remarks 2–3; Appendix A
--   opening paragraphs, PDF p. 11, and Appendix A.1, PDF pp. 11–13.
--   The relevant displays have no equation numbers.
-- source:
--   Arthur Jacot, Franck Gabriel, Clément Hongler, Neural Tangent Kernel: Convergence and Generalization in Neural Networks, NeurIPS 2018, arXiv:1806.07572v4, https://arxiv.org/abs/1806.07572v4; Section 2, PDF p. 2 and PDF p. 3; Section 4.1, PDF p. 5, Proposition 1 and Theorem 1; Appendix A.1, PDF pp. 11–13. Architecture, covariance, and kernel displays are unnumbered.

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Data.Fin.Tuple.Basic

/-!
Finite networks and their initialization laws for Jacot--Gabriel--Hongler,
arXiv:1806.07572v4, Sections 2 and 4.1, PDF pp. 2--5; Appendix A, pp. 11--13.
The referenced architecture, kernel recurrences, and limit conventions are unnumbered displays.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace JGH

/-- Layer `l`, destination neuron, and source neuron (`none` denotes its bias). -/
abbrev ParameterIndex (L : ℕ) (width : ℕ → ℕ) :=
  Σ l : Fin L, Fin (width (l.val + 1)) × Option (Fin (width l.val))

abbrev Parameters (L : ℕ) (width : ℕ → ℕ) := ParameterIndex L width → ℝ

/-- Independent standard normal law on every weight and bias coordinate. -/
def initialization (L : ℕ) (width : ℕ → ℕ) : Measure (Parameters L width) :=
  Measure.pi (fun _ ↦ gaussianReal 0 1)

instance (L : ℕ) (width : ℕ → ℕ) : IsProbabilityMeasure (initialization L width) := by
  unfold initialization
  infer_instance

/-- Preactivations, with the input at layer zero. Values beyond `L` are unused. -/
def preactivation (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L width) (x : Fin (width 0) → ℝ) : (l : ℕ) → Fin (width l) → ℝ
  | 0 => x
  | l + 1 => fun j ↦
      if hl : l < L then
        (∑ i : Fin (width l), θ ⟨⟨l, hl⟩, j, some i⟩ *
          (if l = 0 then preactivation L width σ β θ x l i
            else σ (preactivation L width σ β θ x l i))) / Real.sqrt (width l) +
          β * θ ⟨⟨l, hl⟩, j, none⟩
      else 0

/-- The final affine preactivation, without applying the nonlinearity to the output. -/
def network (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L width) (x : Fin (width 0) → ℝ) : Fin (width L) → ℝ :=
  preactivation L width σ β θ x L

/-- Parameter derivative in a coordinate direction; totalized by Mathlib off differentiability. -/
def parameterDerivative (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L width) (x : Fin (width 0) → ℝ)
    (k : Fin (width L)) (p : ParameterIndex L width) : ℝ := by
  classical
  exact fderiv ℝ (fun η ↦ network L width σ β η x k) θ (Pi.single p 1)

/-- The full weight-and-bias neural tangent kernel, including cross-output entries. -/
def finiteNTK (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L width) (x y : Fin (width 0) → ℝ)
    (k k' : Fin (width L)) : ℝ :=
  ∑ p, parameterDerivative L width σ β θ x k p *
    parameterDerivative L width σ β θ y k' p

abbrev Input (d : ℕ) := Fin d → ℝ
abbrev Kernel (d : ℕ) := Input d → Input d → ℝ

/-- Centered Gaussian pair, allowing singular covariance (in particular, repeated inputs). -/
def gaussianPair {d : ℕ} (K : Kernel d) (x y : Input d) :
    Measure (EuclideanSpace ℝ (Fin 2)) :=
  multivariateGaussian 0 (fun i j ↦ K (![x, y] i) (![x, y] j))

def gaussianProductExpectation {d : ℕ} (K : Kernel d) (φ : ℝ → ℝ)
    (x y : Input d) : ℝ :=
  ∫ z, φ (z 0) * φ (z 1) ∂gaussianPair K x y

/-- Index `h` means network depth `h + 1`, so `h = 0` is the affine base case. -/
def covarianceKernel (d : ℕ) (σ : ℝ → ℝ) (β : ℝ) : ℕ → Kernel d
  | 0 => fun x y ↦ (∑ i, x i * y i) / d + β ^ 2
  | h + 1 => fun x y ↦ gaussianProductExpectation (covarianceKernel d σ β h) σ x y + β ^ 2

/-- The deterministic NTK recurrence in Theorem 1, PDF p. 5. -/
def limitingNTK (d : ℕ) (σ : ℝ → ℝ) (β : ℝ) : ℕ → Kernel d
  | 0 => covarianceKernel d σ β 0
  | h + 1 => fun x y ↦ limitingNTK d σ β h x y *
      gaussianProductExpectation (covarianceKernel d σ β h) (deriv σ) x y +
        covarianceKernel d σ β (h + 1) x y

/-- Positive hidden width `w i + 1`; fixed input and output widths `d` and `q`. -/
def widths {h : ℕ} (d q : ℕ) (w : Fin h → ℕ) (l : ℕ) : ℕ :=
  if l = 0 then d else if hl : l - 1 < h then w ⟨l - 1, hl⟩ + 1 else q

/-- Earlier hidden widths tend to infinity first; the last width is outermost. -/
def sequentialWidths : (h : ℕ) → Filter (Fin h → ℕ)
  | 0 => pure Fin.elim0
  | h + 1 => (atTop : Filter ℕ).bind
      (fun last ↦ (sequentialWidths h).map (fun earlier ↦ Fin.snoc earlier last))

def inputForWidths {h : ℕ} (d q : ℕ) (w : Fin h → ℕ) (x : Input d) :
    Fin (widths d q w 0) → ℝ :=
  fun i ↦ x ⟨i.val, by simpa only [widths, if_pos rfl] using i.isLt⟩

def outputForWidths {h : ℕ} (d q : ℕ) (w : Fin h → ℕ) (k : Fin q) :
    Fin (widths d q w (h + 1)) :=
  ⟨k.val, by simpa only [widths, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
    Nat.lt_irrefl, dite_false] using k.isLt⟩

def initializedOutput {h N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (w : Fin h → ℕ)
    (θ : Parameters (h + 1) (widths d q w)) : EuclideanSpace ℝ (Fin N × Fin q) :=
  WithLp.toLp 2 (fun a ↦ network (h + 1) (widths d q w) σ β θ
    (inputForWidths d q w (X a.1)) (outputForWidths d q w a.2))

/-- Joint limit law on all dataset and output coordinates: independent output GPs. -/
def outputGaussian {N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (h : ℕ) (X : Fin N → Input d) : Measure (EuclideanSpace ℝ (Fin N × Fin q)) :=
  multivariateGaussian 0 (fun a b ↦
    if a.2 = b.2 then covarianceKernel d σ β h (X a.1) (X b.1) else 0)

instance {N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ) (h : ℕ) (X : Fin N → Input d) :
    IsProbabilityMeasure (outputGaussian d q σ β h X) := by
  unfold outputGaussian
  infer_instance

/-- Probability that some entry on the fixed finite dataset exceeds the tolerance. -/
def ntkBadProbability {h N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (ε : ℝ) (w : Fin h → ℕ) : ℝ≥0∞ :=
  initialization (h + 1) (widths d q w) {θ | ∃ i j : Fin N, ∃ k k' : Fin q,
    ε < |finiteNTK (h + 1) (widths d q w) σ β θ
      (inputForWidths d q w (X i)) (inputForWidths d q w (X j))
      (outputForWidths d q w k) (outputForWidths d q w k') -
        (if k = k' then limitingNTK d σ β h (X i) (X j) else 0)|}

end JGH


