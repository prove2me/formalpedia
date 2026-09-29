-- Prove2me | Theorems.Thm_Ising_transfer_pow
-- name    : Ising.transfer_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:54:41.801337+00:00
-- url     : https://prove2.me/theorems/f05dbd40-bd28-40c6-a7cc-49716d43d003
-- title:
--   Closed form of the matrix power.
-- statement:
--   **Closed form of the matrix power.** For every `n`,
--   `T(β)^n = ½ [[λ₊ⁿ+λ₋ⁿ, λ₊ⁿ-λ₋ⁿ], [λ₊ⁿ-λ₋ⁿ, λ₊ⁿ+λ₋ⁿ]]`.
--
--   ```lean
--   theorem Ising.transfer_pow(β : ℝ) (n : ℕ) :
--       (transfer β) ^ n =
--         !![(lamPlus β ^ n + lamMinus β ^ n) / 2, (lamPlus β ^ n - lamMinus β ^ n) / 2;
--            (lamPlus β ^ n - lamMinus β ^ n) / 2, (lamPlus β ^ n + lamMinus β ^ n) / 2] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/IsingModel/TransferMatrix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/IsingModel/TransferMatrix.lean#L84

-- Thm stub generated from Applications/IsingModel/TransferMatrix.lean
import Mathlib
import Definitions.Def_Applications_IsingModel_TransferMatrix

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

open Ising

open Real Matrix

theorem Ising.transfer_pow(β : ℝ) (n : ℕ) :
    (transfer β) ^ n =
      !![(lamPlus β ^ n + lamMinus β ^ n) / 2, (lamPlus β ^ n - lamMinus β ^ n) / 2;
         (lamPlus β ^ n - lamMinus β ^ n) / 2, (lamPlus β ^ n + lamMinus β ^ n) / 2] := by sorry
