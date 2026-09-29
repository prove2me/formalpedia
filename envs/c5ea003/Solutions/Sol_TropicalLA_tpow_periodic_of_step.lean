-- Prove2me | solution 1 for TropicalLA.tpow_periodic_of_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:51:51.969362+00:00
-- url     : https://prove2.me/submissions/9bbda497-4bd3-4558-ab29-66c62dac93a5

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
open TropicalLA Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} {M₀ p : ℕ} {c : ℝ}
    (h : tpow A (M₀ + p) = fun i j => c + tpow A M₀ i j) :
    ∀ m, M₀ ≤ m → tpow A (m + p) = fun i j => c + tpow A m i j := by
  -- a constant shift passes through one more tropical multiplication
  have hshift : ∀ B : Matrix ι ι ℝ,
      tmul (fun i j => c + B i j) A = fun i j => c + tmul B A i j := by
    intro B
    funext i j
    show univ.sup' univ_nonempty (fun k => c + B i k + A k j)
      = c + univ.sup' univ_nonempty (fun k => B i k + A k j)
    apply le_antisymm
    · refine sup'_le _ _ fun k _ => ?_
      have := le_sup' (fun k => B i k + A k j) (mem_univ k)
      linarith
    · obtain ⟨k, -, hk⟩ := exists_mem_eq_sup' univ_nonempty (fun k => B i k + A k j)
      rw [hk]
      have := le_sup' (fun k => c + B i k + A k j) (mem_univ k)
      linarith
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact h
  | succ m hm ih =>
    rw [show m + 1 + p = (m + p) + 1 by ring]
    show tmul (tpow A (m + p)) A = fun i j => c + tmul (tpow A m) A i j
    rw [ih, hshift]
