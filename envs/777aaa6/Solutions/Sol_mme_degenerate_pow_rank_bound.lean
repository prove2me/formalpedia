-- Prove2me | solution 1 for mme_degenerate_pow_rank_bound
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Shuze Chen
-- created : 2026-05-28T20:42:11.862325+00:00
-- url     : https://prove2.me/submissions/1d22576f-8033-46b3-aa36-ce3409f97dee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_degenerate_pow_rank_bound
import Theorems.Thm_mme_kronPow_degenerate
import Theorems.Thm_mme_degenerate_rank_le
import Theorems.Thm_mme_poly_root_tendsto_one

open MME Filter Topology

universe u

/-! # Sketch: border rank ⇒ subexponential rank growth

Decomposition of `mme_degenerate_pow_rank_bound` into:

  * `mme_kronPow_degenerate`     — degeneration is multiplicative under Kronecker powers;
  * `mme_degenerate_rank_le`     — border rank `≤ R` of order `H` gives rank `≤ R·(H+1)^d`;
  * `mme_poly_root_tendsto_one`  — `((n+1)·h+1)^d` is subexponential (`^(1/(n+1)) → 1`).

The sketch extracts the order `h`, picks the overhead `C(m) = ((m·h+1)^d : ℝ)`, and for
each `n` chains `mme_kronPow_degenerate` (power `n+1`) into `mme_degenerate_rank_le`. -/

theorem solution {K : Type u} [Field K] {d : ℕ}
    {X : TensorObj K d} {r : ℕ} (h : Degenerates X (TensorObj.diagObj K d r)) :
    ∃ C : ℕ → ℝ, (∀ n, (1 : ℝ) ≤ C n) ∧
      Filter.Tendsto (fun n => (C (n + 1)) ^ ((1 : ℝ) / (n + 1))) Filter.atTop (nhds 1) ∧
      ∀ n, (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ) ≤ (r : ℝ) ^ (n + 1) * C (n + 1) := by
  obtain ⟨hh, hdeg⟩ := h
  refine ⟨fun m => (((m * hh + 1) ^ d : ℕ) : ℝ), ?_, ?_, ?_⟩
  · intro n
    show (1 : ℝ) ≤ (((n * hh + 1) ^ d : ℕ) : ℝ)
    exact_mod_cast Nat.one_le_pow d (n * hh + 1) (by omega)
  · exact mme_poly_root_tendsto_one hh d
  · intro n
    have h2 := mme_degenerate_rank_le (mme_kronPow_degenerate hdeg (n + 1))
    calc (tensorRankObj (TensorObj.kronPow X (n + 1)) : ℝ)
        ≤ ((r ^ (n + 1) * ((n + 1) * hh + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (r : ℝ) ^ (n + 1) * ((((n + 1) * hh + 1) ^ d : ℕ) : ℝ) := by push_cast; ring
