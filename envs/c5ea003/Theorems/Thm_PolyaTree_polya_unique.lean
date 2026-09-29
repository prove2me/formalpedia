-- Prove2me | Theorems.Thm_PolyaTree_polya_unique
-- name    : PolyaTree.polya_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:04:46.754779+00:00
-- url     : https://prove2.me/theorems/ec008b88-5bd3-4e7c-8f0b-dbc54f87e01c
-- title:
--   Uniqueness.
-- statement:
--   **Uniqueness.** The Pólya tree recurrence with `a₀ = 0, a₁ = 1` has a unique solution.
--   Proved by strong induction: `aₖ` depends only on `a_j` and `ω_{k-j} = Σ_{d|k-j} d·a_d` for
--   `j < k` and `d ≤ k - j < k`, so the base values propagate.
--
--   ```lean
--   theorem PolyaTree.polya_unique(a b : ℕ → ℚ)
--       (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha1 : a 1 = 1) (hb1 : b 1 = 1)
--       (hAr : ∀ k : ℕ, 2 ≤ k →
--         a k = (1 / ((k : ℚ) - 1)) * ∑ j ∈ Finset.Icc 1 (k - 1), a j * omegaSeq a (k - j))
--       (hBr : ∀ k : ℕ, 2 ≤ k →
--         b k = (1 / ((k : ℚ) - 1)) * ∑ j ∈ Finset.Icc 1 (k - 1), b j * omegaSeq b (k - j)) :
--       ∀ n, a n = b n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/PolyaTreeUniqueness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/PolyaTreeUniqueness.lean#L26

-- Thm stub generated from Bridges/PolyaTreeUniqueness.lean
import Mathlib
import Definitions.Def_Bridges_PolyaTreeRecurrence
/-! # Uniqueness of the Pólya tree sequence (Bridges)

The Pólya tree recurrence determines the entire sequence from its base values: any two
sequences `a, b : ℕ → ℚ` with `a₀ = b₀ = 0`, `a₁ = b₁ = 1` that both satisfy

  `aₖ = (1/(k-1)) Σ_{j=1}^{k-1} a_j · ω_{k-j}`   (and likewise for `b`)

are equal at every index. This complements `PolyaTreeRecurrence`: the functional equation
fixes a unique coefficient sequence (OEIS A000081).
-/

open PolyaTree

open Finset

theorem PolyaTree.polya_unique(a b : ℕ → ℚ)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha1 : a 1 = 1) (hb1 : b 1 = 1)
    (hAr : ∀ k : ℕ, 2 ≤ k →
      a k = (1 / ((k : ℚ) - 1)) * ∑ j ∈ Finset.Icc 1 (k - 1), a j * omegaSeq a (k - j))
    (hBr : ∀ k : ℕ, 2 ≤ k →
      b k = (1 / ((k : ℚ) - 1)) * ∑ j ∈ Finset.Icc 1 (k - 1), b j * omegaSeq b (k - j)) :
    ∀ n, a n = b n := by sorry
