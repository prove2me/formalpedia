-- Prove2me | Definitions.Def_mm_spectral
-- name    : mm_spectral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T21:45:16.58486+00:00
-- url     : https://prove2.me/theorems/59462e20-5af9-403d-b93c-75743866077f
-- title:
--   Eigenvalues, spectral gap, relaxation time, and Dirichlet forms
-- statement:
--   This file defines the spectral vocabulary of Chapters 12–13 of Levin–Peres–Wilmer.
--
--   **Eigenvalues and the spectral gap.** An **eigenfunction** of a chain $P$ is a right eigenvector: a nonzero $f:V\to\mathbb R$ with $Pf=\lambda f$, where $(Pf)(x)=\sum_yP(x,y)f(y)$; $\lambda$ is then an eigenvalue. Out of the spectrum the file forms
--   $$\lambda_2=\sup\{\lambda:\ \lambda\ \text{an eigenvalue of}\ P,\ \lambda\ne1\},\qquad \lambda_\star=\sup\{|\lambda|:\ \lambda\ \text{an eigenvalue of}\ P,\ \lambda\ne1\},$$
--   the largest non-unit eigenvalue and the largest non-unit eigenvalue in absolute value. The **spectral gap**, **absolute gap**, and **relaxation time** are
--   $$\gamma=1-\lambda_2,\qquad \gamma_\star=1-\lambda_\star,\qquad t_{\mathrm{rel}}=\frac1{\gamma_\star}.$$
--   For a reversible chain — the standing assumption of the chapter's theorems — all eigenvalues are real with real eigenvectors, so this real-spectrum definition captures the whole spectrum.
--
--   **The geometry of $\ell^2(\pi)$.** The weighted inner product
--   $$\langle f,g\rangle_\pi=\sum_{x}f(x)\,g(x)\,\pi(x)$$
--   is the Hilbert-space structure in which a reversible $P$ is self-adjoint; eigenbases orthonormal for it drive the spectral representation of $P^t$. The **Dirichlet form**
--   $$\mathcal E(f)=\tfrac12\sum_{x,y}\bigl[f(x)-f(y)\bigr]^2\,\pi(x)P(x,y)$$
--   measures the local variation of $f$ along the chain's edges; the variational characterization $\gamma=\min\{\mathcal E(f):\mathbb E_\pi f=0,\ \langle f,f\rangle_\pi=1\}$ is one of this mission's milestones.
--
--   **The $n$-cycle.** Simple (non-lazy) random walk on $\mathbb Z_n$, stepping to $x\pm1$ with probability $\tfrac12$ each — the model chain whose eigenvalues $\cos(2\pi j/n)$ are computed as a milestone.
--
--   **Conventions.** The suprema defining $\lambda_2$ and $\lambda_\star$ are taken in $\mathbb R$ and evaluate to the junk value $0$ when the set of non-unit eigenvalues is empty (e.g. a one-point space); the theorems affected assume at least two states. Inversion is total ($0^{-1}=0$), so $t_{\mathrm{rel}}$ is always defined.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 12-13, Sections 12.1-12.2, 12.3.1, 13.3, pp. 153-156 and 175-176

import Definitions.Def_mm_mixing
import Definitions.Def_mm_lower

/-!
Eigenvalues, spectral gap, relaxation time, and Dirichlet forms, following
Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapters 12–13.

Eigenfunctions are right eigenvectors: `P f = λ f` with
`(Pf)(x) = ∑_y P(x,y) f(y)`.  For a chain reversible with respect to `π`,
all eigenvalues are real and `ℓ²(π)` has an orthonormal eigenbasis
(Lemma 12.2), so the definitions below capture the whole spectrum.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `λ` is an **eigenvalue** of `P`, with a (real) eigenfunction
(LPW §12.1). -/
def IsEigenvalue (P : Matrix V V ℝ) (lam : ℝ) : Prop :=
  ∃ f : V → ℝ, f ≠ 0 ∧ P.mulVec f = lam • f

/-- `λ₂`, the largest eigenvalue different from `1` (for an irreducible
reversible chain, the second largest eigenvalue; LPW §12.2). -/
def lambdaTwo (P : Matrix V V ℝ) : ℝ :=
  sSup {lam : ℝ | IsEigenvalue P lam ∧ lam ≠ 1}

/-- `λ⋆ = max {|λ| : λ an eigenvalue of P, λ ≠ 1}` (LPW §12.2). -/
def lambdaStar (P : Matrix V V ℝ) : ℝ :=
  sSup {r : ℝ | ∃ lam : ℝ, IsEigenvalue P lam ∧ lam ≠ 1 ∧ r = |lam|}

/-- The **spectral gap** `γ = 1 − λ₂` (LPW §12.2). -/
def spectralGap (P : Matrix V V ℝ) : ℝ :=
  1 - lambdaTwo P

/-- The **absolute spectral gap** `γ⋆ = 1 − λ⋆` (LPW §12.2). -/
def absSpectralGap (P : Matrix V V ℝ) : ℝ :=
  1 - lambdaStar P

/-- The **relaxation time** `t_rel = 1/γ⋆` (LPW §12.2). -/
def relaxationTime (P : Matrix V V ℝ) : ℝ :=
  (absSpectralGap P)⁻¹

/-- The inner product `⟨f,g⟩_π = ∑_x f(x) g(x) π(x)` on `ℓ²(π)`
(LPW §12.1, Eq. (12.1)). -/
def innerPi (π : V → ℝ) (f g : V → ℝ) : ℝ :=
  ∑ x, f x * g x * π x

/-- The **Dirichlet form**
`E(f) = ½ ∑_{x,y} [f(x) − f(y)]² π(x) P(x,y)` (LPW §13.3,
Eq. (13.11)). -/
def dirichletForm (P : Matrix V V ℝ) (π : V → ℝ) (f : V → ℝ) : ℝ :=
  2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y)

/-- Simple random walk on the `n`-cycle `ℤ_n` (LPW §12.3.1; take `n ≥ 3`). -/
def cycleWalk (n : ℕ) : Matrix (ZMod n) (ZMod n) ℝ :=
  fun x y => if y = x + 1 ∨ y = x - 1 then 1 / 2 else 0

end

end MarkovMixing


