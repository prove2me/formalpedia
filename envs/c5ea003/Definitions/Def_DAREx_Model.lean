-- Prove2me | Definitions.Def_DAREx_Model
-- name    : DAREx_Model
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-29T05:56:29.398305+00:00
-- url     : https://prove2.me/theorems/2cbbddff-3e3b-46be-bd5c-486a83a4e812
-- title:
--   DARE pruning model — masks, rescaling, and coefficient statistics
-- statement:
--   Fix a natural number $n$ and deterministic real coefficients $c_j$, indexed by $j\in\{1,\ldots,n\}$. A Boolean mask $\omega$ records dropped coordinates. For $0\le p\le1$, it has mass $w_p(\omega)=\prod_j[p\text{ if }\omega_j=1;\;1-p\text{ otherwise}]$, so the drops are independent Bernoulli variables of parameter $p$. The bundle defines expectation and event probability as the finite weighted sums and proves nonnegative masses and total mass one.
--
--   Write $S=\sum_jc_j$, $Q=\sum_jc_j^2$, $\bar c=S/n$, and $\sigma^2=n^{-1}\sum_j(c_j-\bar c)^2$. The statistical identities using these last two quantities require $n>0$. For a positive rescaling denominator $q$, set $H_q(\omega)=\sum_jc_j(1-(1-\omega_j)/q)$ and $b_q=(1-(1-p)/q)S$. DARE uses $H=H_{1-p}$ for $0<p<1$. Define $\Phi(1/2)=1/2$ and $\Phi(p)=(1-2p)/\log((1-p)/p)$ otherwise; concentration theorems restrict $p$ to $(0,1)$.
--
--   **Formalization note.** Finite-sum encoding of the paper's Bernoulli probability model: true means dropped, the complement of its retention variable. Definitions are total Lean functions; no probability or analytic claim is made outside the stated domains. The model is not an assumption of any concentration conclusion. Primary reference: Deng et al., Section 3.2, PDF p. 5, equation (2); Appendix E.1, PDF pp. 29–31, equations (7)–(8); Appendix E.2, PDF p. 31, initial unnumbered identity. See the linked source.
-- source:
--   Deng et al., DARE the Extreme: Revisiting Delta-Parameter Pruning For Fine-Tuned Models, ICLR 2025, arXiv:2410.09344v2, https://arxiv.org/pdf/2410.09344v2, Section 3.2, PDF p. 5, equation (2); Appendix E.1, PDF pp. 29–31, equations (7)–(8).

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open scoped BigOperators

namespace DAREx

/-- A true bit denotes a dropped coordinate. -/
abbrev Mask (n : ℕ) := Fin n → Bool

/-- Product law of independent Bernoulli drop indicators. -/
def maskMass {n : ℕ} (p : ℝ) (ω : Mask n) : ℝ :=
  ∏ j, if ω j then p else 1 - p

def mean {n : ℕ} (p : ℝ) (f : Mask n → ℝ) : ℝ :=
  ∑ ω, maskMass p ω * f ω

def probability {n : ℕ} (p : ℝ) (event : Mask n → Prop) : ℝ := by
  classical
  exact ∑ ω, if event ω then maskMass p ω else 0

def coefficientSum {n : ℕ} (c : Fin n → ℝ) : ℝ := ∑ j, c j

def energy {n : ℕ} (c : Fin n → ℝ) : ℝ := ∑ j, c j ^ 2

def empiricalMean {n : ℕ} (c : Fin n → ℝ) : ℝ := coefficientSum c / n

def empiricalVariance {n : ℕ} (c : Fin n → ℝ) : ℝ :=
  (∑ j, (c j - empiricalMean c) ^ 2) / n

/-- Original output minus pruned output, with surviving weights rescaled by `1/q`. -/
def outputError {n : ℕ} (q : ℝ) (c : Fin n → ℝ) (ω : Mask n) : ℝ :=
  ∑ j, (c j - (if ω j then 0 else c j / q))

def dareError {n : ℕ} (p : ℝ) (c : Fin n → ℝ) : Mask n → ℝ :=
  outputError (1 - p) c

def outputBias {n : ℕ} (p q : ℝ) (c : Fin n → ℝ) : ℝ :=
  (1 - (1 - p) / q) * coefficientSum c

/-- Continuous value at one half; analytic claims use `0 < p < 1`. -/
def phi (p : ℝ) : ℝ :=
  if p = 1 / 2 then 1 / 2 else (1 - 2 * p) / Real.log ((1 - p) / p)

lemma maskMass_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (ω : Mask n) :
    0 ≤ maskMass p ω := by
  apply Finset.prod_nonneg
  intro j _
  split
  · exact hp
  · exact sub_nonneg.mpr hp'

lemma maskMass_sum {n : ℕ} (p : ℝ) : ∑ ω : Mask n, maskMass p ω = 1 := by
  unfold maskMass
  simpa using (Fintype.prod_sum (fun (_ : Fin n) (b : Bool) ↦
    if b then p else 1 - p)).symm

end DAREx


