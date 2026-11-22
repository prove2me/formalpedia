-- Prove2me | Definitions.Def_erdos390_prime_power_rounding
-- name    : erdos390_prime_power_rounding
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-16T13:58:21.718109+00:00
-- url     : https://prove2.me/theorems/de262482-a5b0-430d-b767-d05dc0d78257
-- title:
--   Prime-power columns, valuation errors and complete rough signatures
-- statement:
--   For an integer upper bound $M$, the finite column family consists of $(p,j)$ with $p$ prime, $j\ge1$ and $p^j\le M$. Its incidence with a positive integer $a$ is $p^j\mid a$. For candidate values $a_i$ and real vectors $X,x$, define
--   $$e_p(X,x)=\sum_i(X_i-x_i)v_p(a_i).$$
--   The complete rough signature at cutoff $y$ is the finitely supported vector $(v_p(a)\mathbf1_{p>y})_p$. These definitions express the degree estimate, prime-valuation discrepancy, and exact cancellation of large-prime errors in the rounding stage.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 10, equations rounding-prime-power-column, rounding-error-sign, rounding-no-rough-error. https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex; PrimePowerColumns.lean, ValuationError.lean and BankRoughSignatures.lean.

import Definitions.Def_erdos390_floating_rounding

open scoped BigOperators
namespace Erdos390.WholePaper
noncomputable section

def primePowerColumns (M : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 2 M).product (Finset.Icc 1 M)).filter fun q ↦
    q.1.Prime ∧ q.1 ^ q.2 ≤ M

@[simp]
theorem mem_primePowerColumns {M p j : ℕ} :
    (p, j) ∈ primePowerColumns M ↔
      2 ≤ p ∧ p ≤ M ∧ 1 ≤ j ∧ j ≤ M ∧ p.Prime ∧ p ^ j ≤ M := by
  classical
  simp [primePowerColumns, and_assoc, and_left_comm, and_comm]

def primePowerInc (M : ℕ) (q : ↥(primePowerColumns M)) (a : ℕ) : Prop :=
  q.1.1 ^ q.1.2 ∣ a

def roundingValuationError {A : Type*} [Fintype A]
    (value : A → ℕ) (X x : A → ℝ) (p : ℕ) : ℝ :=
  ∑ a, (X a - x a) * (value a).factorization p

def completeRoughSignature (y a : ℕ) : ℕ →₀ ℕ :=
  a.factorization.filter (fun p ↦ y < p)

/-- Coordinate description of the complete rough signature. -/
theorem completeRoughSignature_apply (y a p : ℕ) :
    completeRoughSignature y a p =
      if y < p then a.factorization p else 0 := rfl


end
end Erdos390.WholePaper


