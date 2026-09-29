-- Prove2me | Theorems.Thm_CyclicTypeChannel_gibbs_double
-- name    : CyclicTypeChannel.gibbs_double
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:30:18.869973+00:00
-- url     : https://prove2.me/theorems/38ecb4df-6012-425a-b4b2-0cb76cc776ab
-- title:
--   Gibbs' inequality for a joint count array.
-- statement:
--   **Gibbs' inequality for a joint count array.** If `n c v` is a non-negative
--   array whose row sums are `M c`, and `m v`, `M c` are positive marginals adding
--   up to `N`, then the mutual-information sum is non-negative.
--
--   ```lean
--   theorem CyclicTypeChannel.gibbs_double(C : Finset γ) (T : Finset β) (N : ℝ) (hN : 0 < N)
--       (n : γ → β → ℝ) (m : β → ℝ) (M : γ → ℝ)
--       (hn : ∀ c v, 0 ≤ n c v) (hm : ∀ v ∈ T, 0 < m v) (hM : ∀ c ∈ C, 0 < M c)
--       (hsm : ∑ v ∈ T, m v = N) (hsM : ∑ c ∈ C, M c = N)
--       (hnv : ∀ c ∈ C, ∑ v ∈ T, n c v = M c) :
--       0 ≤ ∑ c ∈ C, ∑ v ∈ T,
--         (n c v / N) *
--           (Real.logb 2 N - Real.logb 2 (m v) - Real.logb 2 (M c) + Real.logb 2 (n c v)) := by sorry
--   /-! ## 2. The joint count array of two read-outs -/
--
--
--   variable (s : Finset α) (g : α → β) (k : α → γ)
--
--
--
--
--
--
--
--   /-! ## 3. Non-negativity -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelNonneg.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelNonneg.lean#L46

-- Thm stub generated from Shared/CyclicTypeChannelNonneg.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
/-
# Non-negativity of the counting mutual information

The channel quantities used for the cyclic splitting-type channel are honest
information-theoretic objects: this file proves the Gibbs inequality for the
counting framework, i.e. `I(g ; k) ≥ 0` for every pair of read-outs of a finite
uniform source, and derives the sandwich `0 ≤ I(g ; k) ≤ H(g)`.

The proof is the classical one: `I` is the Kullback–Leibler divergence between
the joint law and the product of the marginals, and `log t ≤ t - 1`.
-/

open CyclicTypeChannel

open Finset

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ]

/-! ## 1. The analytic core -/


omit [DecidableEq β] [DecidableEq γ] in

theorem CyclicTypeChannel.gibbs_double(C : Finset γ) (T : Finset β) (N : ℝ) (hN : 0 < N)
    (n : γ → β → ℝ) (m : β → ℝ) (M : γ → ℝ)
    (hn : ∀ c v, 0 ≤ n c v) (hm : ∀ v ∈ T, 0 < m v) (hM : ∀ c ∈ C, 0 < M c)
    (hsm : ∑ v ∈ T, m v = N) (hsM : ∑ c ∈ C, M c = N)
    (hnv : ∀ c ∈ C, ∑ v ∈ T, n c v = M c) :
    0 ≤ ∑ c ∈ C, ∑ v ∈ T,
      (n c v / N) *
        (Real.logb 2 N - Real.logb 2 (m v) - Real.logb 2 (M c) + Real.logb 2 (n c v)) := by sorry
