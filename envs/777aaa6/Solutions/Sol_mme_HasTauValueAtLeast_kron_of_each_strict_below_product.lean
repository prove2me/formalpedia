-- Prove2me | solution 1 for mme_HasTauValueAtLeast_kron_of_each_strict_below_product
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T04:21:26.216064+00:00
-- url     : https://prove2.me/submissions/4abaf62c-3b34-4728-b845-e7932b184dac

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_CW_2376_address_block
import Theorems.Thm_mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME BigOperators

universe u

set_option autoImplicit false

private theorem kronFin_two_kronPow_one_isomorphic
    {K : Type u} [Field K] {d : ℕ} (X Y : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.kronFin 2 (fun i => (![X, Y] i).kronPow 1))
      (TensorObj.kron X Y) := by
  apply TensorQ.toQ_eq_iff.mp
  show TensorQ.toQ (TensorObj.kron ((![X, Y] 0).kronPow 1)
      (TensorObj.kron ((![X, Y] (0 : Fin 1).succ).kronPow 1)
        (TensorObj.kronFin 0 (fun i => (![X, Y] i.succ.succ).kronPow 1)))) = _
  show TensorQ.toQ (TensorObj.kron (X.kronPow 1)
      (TensorObj.kron (Y.kronPow 1) TensorObj.oneObj)) = _
  rw [TensorQ.toQ_kron, TensorQ.toQ_kron, TensorQ.toQ_kron,
    TensorQ.toQ_kronPow, TensorQ.toQ_kronPow]
  show _ = _
  rw [pow_one, pow_one, ← TensorQ.toQ_one, mul_one]

theorem solution
    {K : Type u} [Field K]
    (X Y : TensorObj K 3) (tau eX eY : ℝ)
    (heX : 0 < eX) (heY : 0 < eY)
    (hX : ∀ V : ℝ, 0 ≤ V → V < eX → HasTauValueAtLeast X tau V)
    (hY : ∀ V : ℝ, 0 ≤ V → V < eY → HasTauValueAtLeast Y tau V) :
    ∀ W : ℝ, 0 ≤ W → W < eX * eY →
      HasTauValueAtLeast (TensorObj.kron X Y) tau W := by
  intro W hW hWlt
  have hend : ∀ i : Fin 2, 0 < (![eX, eY] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simpa
  have hloc : ∀ (i : Fin 2) (V : ℝ), 0 ≤ V → V < (![eX, eY] : Fin 2 → ℝ) i →
      HasTauValueAtLeast (![X, Y] i) tau V := by
    intro i V h0 h1
    fin_cases i
    · exact hX V h0 (by simpa using h1)
    · exact hY V h0 (by simpa using h1)
  have hmul :=
    mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
      (K := K) (n := 2) ![X, Y] ![1, 1] tau ![eX, eY] hend hloc
      W hW (by simpa [Fin.prod_univ_two] using hWlt)
  exact mme_HasTauValueAtLeast_mono_restrict
    (kronFin_two_kronPow_one_isomorphic X Y).1 hmul
