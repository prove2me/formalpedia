-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss
-- name    : mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T07:18:22.122329+00:00
-- url     : https://prove2.me/theorems/f661ffee-5423-49fe-a51b-87a1a1cf2327
-- title:
--   Uniform square blocks in even coupled powers with square-root loss
-- statement:
--   For every real $\tau$ with $3\tau\ge2$ and every field $K$, there is $C\ge0$ such that, for all sufficiently large $N$, set $L=\lfloor 2N/(6^{3\tau}+2)\rfloor$, $G=N-L$, and $s=6^{4G+2L}$. The $2N$th tensor power of the cyclic symmetrization of the coupled $q=6$ tensor restricts to $k$ identical copies of $\langle s,s,s\rangle$, with $k(s^3)^\tau\ge [4\cdot6^{3\tau}(6^{3\tau}+2)]^{2N}\exp(-C\sqrt{N+1})$. This preserves the exact square shape as well as the finite weighted count.
-- source:
--   Uniform primary hash dimensions, outer-family square extraction, and the bounded primary hash capacity estimate.

import Definitions.Def_mme_CW_coupled_value
import Mathlib.Tactic
open MME BigOperators Filter
universe u
set_option autoImplicit false

theorem mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let L : ℕ := ⌊2 / ((6 : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊
        let G : ℕ := N - L
        let side : ℕ := 6 ^ (4 * G + 2 * L)
        ∃ k : ℕ,
          TensorObj.Restrict
            (TensorObj.bigAdd (fun _ : Fin k ↦ MMObj K side side side))
            ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
          (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^ (2 * N) *
              Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            (k : ℝ) * (((side ^ 3 : ℕ) : ℝ) ^ tau) := by sorry
