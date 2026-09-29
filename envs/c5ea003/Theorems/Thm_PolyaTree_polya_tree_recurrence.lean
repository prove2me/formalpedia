-- Prove2me | Theorems.Thm_PolyaTree_polya_tree_recurrence
-- name    : PolyaTree.polya_tree_recurrence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:04:36.260565+00:00
-- url     : https://prove2.me/theorems/0bf2eb6f-93ac-4596-8fd2-fc448c7384ab
-- title:
--   Pólya tree recurrence (main result).
-- statement:
--   **Pólya tree recurrence (main result).** If the Pólya tree generating-function identity
--   holds in log-derivative form and `a₁ = 1`, then `a₁ = 1` and for every `k ≥ 2`
--
--     `aₖ = (1/(k-1)) · Σ_{j=1}^{k-1} a_j · ω_{k-j}`,   `ωₘ = Σ_{d ∣ m} d·a_d`.
--
--   This is exactly the statement of the research concept.
--
--   ```lean
--   theorem PolyaTree.polya_tree_recurrence(a : ℕ → ℚ) (ha1 : a 1 = 1)
--       (hFE : ∀ n : ℕ, 1 ≤ n →
--         (n : ℚ) * a n =
--           a n + ∑ j ∈ Finset.Icc 1 (n - 1), a j * (((n - j : ℕ) : ℚ) * sCoeff a (n - j))) :
--       a 1 = 1 ∧ ∀ k : ℕ, 2 ≤ k →
--         a k = (1 / ((k : ℚ) - 1)) * ∑ j ∈ Finset.Icc 1 (k - 1), a j * omegaSeq a (k - j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/PolyaTreeRecurrence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/PolyaTreeRecurrence.lean#L102

-- Thm stub generated from Bridges/PolyaTreeRecurrence.lean
import Mathlib
import Definitions.Def_Bridges_PolyaTreeRecurrence

/-! # Pólya tree coefficient recurrence formula (Bridges)

This file formalizes the classical bridge between the **functional equation** for the
ordinary generating function of rooted (unlabelled) trees — *Pólya trees* — and the
**coefficient recurrence** used to enumerate them (OEIS A000081).

Let `A(z) = Σ_{k≥1} aₖ zᵏ` be the Pólya tree generating function, characterised by

  `A(z) = z · exp(A(z)) · Φ(z)`,   `Φ(z) = exp(Σ_{i≥2} A(zⁱ)/i)`.

Writing `S(z) = Σ_{i≥1} A(zⁱ)/i` (so `A = z·exp(S)`), and taking the logarithmic
derivative of the functional equation gives the *exp-free* identity

  `z·A'(z) = A(z)·(1 + z·S'(z))`.                                        (LD)

The arithmetic weight `ωₖ = Σ_{d|k} d·a_d` enters through the divisor identity

  `[zⁿ] (z·S'(z)) = n · [zⁿ] S(z) = n · Σ_{i|n} a_{n/i}/i = Σ_{d|n} d·a_d = ωₙ`.   (DB)

Combining (LD) and (DB) and extracting coefficients yields, for `k ≥ 2`,

  `aₖ = (1/(k-1)) · Σ_{j=1}^{k-1} a_j · ω_{k-j}`,    with `a₁ = 1`.

The mathematical heart of the bridge is the **divisor identity (DB)** (`divisor_bridge`),
which is what connects the analytic object `S(z) = Σ_{i≥1} A(zⁱ)/i` to the
number-theoretic divisor weight `ωₖ`. Everything else is Cauchy-product bookkeeping.

References (catalog): Cayley's tree enumeration (MR1577579), Pólya's counting theory
(MR0025715), and the analytic-combinatorics treatment of tree functional equations
(MR2483235).

## Main statements
* `divisor_bridge`   : `n · sCoeff a n = omegaSeq a n` — the log-derivative ↔ divisor weight bridge.
* `polya_FE_iff_recurrence` : the functional-equation log-derivative identity is *equivalent*
  to the Pólya tree recurrence.
* `polya_tree_recurrence` : the explicit recurrence `aₖ = (1/(k-1)) Σ a_j ω_{k-j}` for `k ≥ 2`.
-/

open PolyaTree

open Finset

theorem PolyaTree.polya_tree_recurrence(a : ℕ → ℚ) (ha1 : a 1 = 1)
    (hFE : ∀ n : ℕ, 1 ≤ n →
      (n : ℚ) * a n =
        a n + ∑ j ∈ Finset.Icc 1 (n - 1), a j * (((n - j : ℕ) : ℚ) * sCoeff a (n - j))) :
    a 1 = 1 ∧ ∀ k : ℕ, 2 ≤ k →
      a k = (1 / ((k : ℚ) - 1)) * ∑ j ∈ Finset.Icc 1 (k - 1), a j * omegaSeq a (k - j) := by sorry
