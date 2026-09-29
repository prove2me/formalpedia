-- Prove2me | Definitions.Def_Applications_IsingModel_TransferMatrix
-- name    : Applications_IsingModel_TransferMatrix
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:22.897595+00:00
-- url     : https://prove2.me/theorems/cbb304f9-9fa3-4ec1-8f2d-1000c7524d68
-- title:
--   Aether Catalog definitions — Applications_IsingModel_TransferMatrix
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.IsingModel.TransferMatrix`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/IsingModel/TransferMatrix.lean by skeleton subtraction
import Mathlib

/-!
# 2D Ising Model: The Transfer Matrix Method (1D row transfer)

We construct the `2 × 2` transfer matrix of the Ising model with zero external
field (units `J = k_B = 1`),
`T(β) = [[e^{β}, e^{-β}], [e^{-β}, e^{β}]]`,
diagonalise it, and use it to compute the partition function of a periodic chain
of `N` spins as the trace of `T(β)^N`.  This is the algebraic engine underlying
Onsager's solution: the two eigenvalues are
`λ₊ = 2 cosh β` (symmetric mode) and `λ₋ = 2 sinh β` (antisymmetric mode), and
`Z_N = Tr T^N = λ₊^N + λ₋^N`.

-- !-- Lab Notes -- !--
* **Hypothesis.** `(1,1)` and `(1,-1)` are eigenvectors of `T(β)` with eigenvalues
  `2 cosh β`, `2 sinh β`; hence `Tr T^N = (2cosh β)^N + (2 sinh β)^N`.
* **Experiment.** Verify eigenvector equations by `Fin.sum_univ_two` + `cosh/sinh`
  exponential forms. For the power, guess the closed form
  `T^n = ½[[λ₊ⁿ+λ₋ⁿ, λ₊ⁿ-λ₋ⁿ],[λ₊ⁿ-λ₋ⁿ, λ₊ⁿ+λ₋ⁿ]]` and prove by induction; the
  step collapses because `λ₊·e^{±β}` and `λ₋·e^{±β}` recombine into `λ₊^{n+1}`,
  `λ₋^{n+1}` (lemmas `e1`, `e2` use `λ₊ = e^β+e^{-β}`, `λ₋ = e^β-e^{-β}`).
* **Analysis.** Survives. The induction is the crux; the trace formula is then a
  one-liner. The eigenvalue *dominance* `λ₊ > λ₋` (strict for all β) explains why
  the free energy per site tends to `log λ₊ = log(2 cosh β)`.
* **Critique.** No theorem is trivial: the closed form requires a genuine matrix
  induction (`pow_succ`, `Matrix.mul_apply`, `Fin.sum_univ_two`) and
  `ring`/exponential identities; eigenvalue facts use `Real.cosh`/`Real.sinh`,
  not `rfl`.
* **Synthesis.** `Z_N = λ₊^N + λ₋^N` with `λ₊ = 2cosh β`, `λ₋ = 2 sinh β`.
-/

namespace Ising

open Real Matrix

/-- The Ising transfer matrix `T(β) = [[e^{β}, e^{-β}], [e^{-β}, e^{β}]]`. -/
noncomputable def transfer (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp β, Real.exp (-β); Real.exp (-β), Real.exp β]

/-- Larger eigenvalue (symmetric mode): `λ₊ = 2 cosh β`. -/
noncomputable def lamPlus (β : ℝ) : ℝ := 2 * Real.cosh β

/-- Smaller eigenvalue (antisymmetric mode): `λ₋ = 2 sinh β`. -/
noncomputable def lamMinus (β : ℝ) : ℝ := 2 * Real.sinh β









/-- The partition function of a periodic Ising chain of `N` spins. -/
noncomputable def partitionFunction (β : ℝ) (N : ℕ) : ℝ := ((transfer β) ^ N).trace



end Ising


