-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_Ctensor_finite_capacity
-- name    : mme_CW_q6_primary_hash_Ctensor_finite_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:35:13.679535+00:00
-- url     : https://prove2.me/theorems/96791381-2f9f-407a-be15-d7fb564f4aed
-- title:
--   Finite first-hash C-tensor extraction at the exact coupled q=6 capacity
-- statement:
--   Fix a field \(K\), a real \(\tau\) with \(3\tau\ge2\), and the coupled \(q=6\) profile
--   \[
--   L=\left\lfloor\frac{2N}{6^{3\tau}+2}\right\rfloor,\qquad G=N-L.
--   \]
--   Assume \(L>0\), \(L+G=N\), and \(341L<100G\).  Define
--   \[
--   Z=\binom{2N}{L}\binom{2N-L}{L},\qquad
--   X=\binom NG,\qquad B=\binom{2G}{G},
--   \]
--   and the finite C-tensor capacity
--   \[
--   \mathcal C_{N,L,G}=\frac{Z^3B^2}{16X^4}.
--   \]
--   For all sufficiently large \(N\), the first Salem--Spencer hashing and equal-fiber pruning produce positive integers \(A,H\), with \(H\le4^N\), and an actual coordinate restriction of the cyclic source power to
--   \[
--   \bigoplus_{a=1}^{A^3}
--     \left(\langle H,H,H\rangle\otimes S_{L,G}\right).
--   \]
--   For \(\delta_N=(N+1)^{-1/4}\), the retained parameters satisfy
--   \[
--   \mathcal C_{N,L,G}e^{-N\delta_N/2}\le A^3H^2.
--   \]
--
--   This theorem is solely the first Behrend/hash/pruning stage.  The shared-index multiplicity remains encoded by \(\langle H,H,H\rangle\); no exact \(H^2\) direct-sum extraction is asserted.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--272: Z-block multinomial count, modulus M=4*binom(N,G)^2+1, Salem--Spencer hashing, C-tensor multiplicity H approximately binom(2G,G)/(4*binom(N,G)^2), and the condition G/L>3.41; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_CW_q6_coupled_survivor
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open MME BigOperators Filter Topology
universe u

theorem mme_CW_q6_primary_hash_Ctensor_finite_capacity
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let capacity : ℝ :=
        ((Zcount : ℝ) ^ 3 * (middle : ℝ) ^ 2) /
          (16 * (Xcount : ℝ) ^ 4)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ,
        0 < H ∧
        H ≤ 4 ^ N ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
            TensorObj.kron (MMObj K H H H)
              (coupledQ6Survivor K L Gcount)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        capacity * Real.exp (-((N : ℝ) * loss / 2)) ≤
          ((A ^ 3 : ℕ) : ℝ) * ((H : ℝ) ^ 2) := by sorry
