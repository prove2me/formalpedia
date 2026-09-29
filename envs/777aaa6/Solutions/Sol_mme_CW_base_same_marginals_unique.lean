-- Prove2me | solution 1 for mme_CW_base_same_marginals_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T06:31:40.85798+00:00
-- url     : https://prove2.me/submissions/eb7e3727-5062-4e25-b7b9-b66aa4d87b09

import Definitions.Def_mme_modern_entropy_data
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem marginal_sum (coord : Fin 6 → Fin 3) (p : Fin 6 → ℝ) (k : Fin 3) :
    mme_modern_marginal coord p k = ∑ a, if coord a = k then p a else 0 := by
  classical
  unfold mme_modern_marginal
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a ↦ coord a = k))
    (by simp) p]
  exact Finset.sum_filter _ _

theorem solution (rho alpha : Fin 6 → ℝ)
    (hX : ∀ k : Fin 3,
      mme_modern_marginal (![0, 0, 0, 1, 1, 2] : Fin 6 → Fin 3) rho k =
        mme_modern_marginal (![0, 0, 0, 1, 1, 2] : Fin 6 → Fin 3) alpha k)
    (hY : ∀ k : Fin 3,
      mme_modern_marginal (![0, 1, 2, 0, 1, 0] : Fin 6 → Fin 3) rho k =
        mme_modern_marginal (![0, 1, 2, 0, 1, 0] : Fin 6 → Fin 3) alpha k)
    (hZ : ∀ k : Fin 3,
      mme_modern_marginal (![2, 1, 0, 1, 0, 0] : Fin 6 → Fin 3) rho k =
        mme_modern_marginal (![2, 1, 0, 1, 0, 0] : Fin 6 → Fin 3) alpha k) :
    rho = alpha ∧ mme_modern_entropyBits rho = mme_modern_entropyBits alpha := by
  have hx1 := hX 1
  have hy1 := hY 1
  have hz1 := hZ 1
  have hx2 := hX 2
  have hy2 := hY 2
  have hz2 := hZ 2
  simp only [marginal_sum] at hx1 hy1 hz1 hx2 hy2 hz2
  norm_num [Fin.sum_univ_succ, Fin.ext_iff] at hx1 hy1 hz1 hx2 hy2 hz2
  change rho 3 + rho 4 = alpha 3 + alpha 4 at hx1
  change rho 1 + rho 4 = alpha 1 + alpha 4 at hy1
  change rho 1 + rho 3 = alpha 1 + alpha 3 at hz1
  change rho 5 = alpha 5 at hx2
  have heq : rho = alpha := by
    funext i
    fin_cases i
    · exact hz2
    · change rho 1 = alpha 1
      linarith only [hx1, hy1, hz1]
    · exact hy2
    · change rho 3 = alpha 3
      linarith only [hx1, hy1, hz1]
    · change rho 4 = alpha 4
      linarith only [hx1, hy1, hz1]
    · exact hx2
  exact ⟨heq, congrArg mme_modern_entropyBits heq⟩
