-- Prove2me | Theorems.Thm_PolyaTree_polya_FE_iff_recurrence
-- name    : PolyaTree.polya_FE_iff_recurrence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:04:43.692629+00:00
-- url     : https://prove2.me/theorems/ce441a00-de19-4b93-97d5-441edcb680d8
-- title:
--   Bridge equivalence.
-- statement:
--   **Bridge equivalence.** For any coefficient sequence `a`, the log-derivative form of the
--   Pólya tree functional equation `z·A'(z) = A(z)·(1 + z·S'(z))` (expressed coefficientwise via
--   `sCoeff`) is *equivalent* to the Pólya tree recurrence `(k-1)·aₖ = Σ_{j} a_j·ω_{k-j}`.
--
--   The forward direction extracts coefficients of (LD); the reverse re-assembles them. Both
--   directions route through `divisor_bridge`, which is the only non-formal ingredient. The
--   `n = 1` instance of the left-hand identity is vacuous (`1·a₁ = a₁`), matching the fact that
--   the recurrence only constrains `k ≥ 2`.
--
--   ```lean
--   theorem PolyaTree.polya_FE_iff_recurrence(a : ℕ → ℚ) :
--       (∀ n : ℕ, 1 ≤ n →
--         (n : ℚ) * a n =
--           a n + ∑ j ∈ Finset.Icc 1 (n - 1), a j * (((n - j : ℕ) : ℚ) * sCoeff a (n - j)))
--       ↔ (∀ k : ℕ, 2 ≤ k →
--         ((k : ℚ) - 1) * a k = ∑ j ∈ Finset.Icc 1 (k - 1), a j * omegaSeq a (k - j)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/PolyaTreeRecurrence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/PolyaTreeRecurrence.lean#L73

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

theorem PolyaTree.polya_FE_iff_recurrence(a : ℕ → ℚ) :
    (∀ n : ℕ, 1 ≤ n →
      (n : ℚ) * a n =
        a n + ∑ j ∈ Finset.Icc 1 (n - 1), a j * (((n - j : ℕ) : ℚ) * sCoeff a (n - j)))
    ↔ (∀ k : ℕ, 2 ≤ k →
      ((k : ℚ) - 1) * a k = ∑ j ∈ Finset.Icc 1 (k - 1), a j * omegaSeq a (k - j)) := by sorry
