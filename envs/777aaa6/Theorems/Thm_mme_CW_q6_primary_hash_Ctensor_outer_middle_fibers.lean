-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_Ctensor_outer_middle_fibers
-- name    : mme_CW_q6_primary_hash_Ctensor_outer_middle_fibers
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T17:41:21.192305+00:00
-- url     : https://prove2.me/theorems/c4afe078-7990-4bcc-8dc5-c6776e1d92a1
-- title:
--   Finite q=6 first-hash outer-family and common C-tensor fiber bounds
-- statement:
--   Fix a field \(K\), a real \(\tau\) with \(3\tau\ge 2\), and the coupled \(q=6\) profile \(L=\lfloor 2N/(6^{3\tau}+2)\rfloor\), \(G=N-L\). Write \(Z=\binom{2N}{L}\binom{2N-L}{L}\), \(X=\binom NG\), \(B=\binom{2G}{G}\), and \(\delta_N=(N+1)^{-1/4}\). Under the source pruning conditions \(L>0\), \(L+G=N\), and \(341L<100G\), for every sufficiently large \(N\) the first Salem--Spencer hashing and equal-fiber pruning produce integers \(A,H\), with \(0<H\le4^N\), and an actual restriction to \(A^3\) macro blocks
--   \[
--   \bigoplus_{a=1}^{A^3} \bigl(\langle H,H,H\rangle\otimes S_{L,G}\bigr).
--   \]
--   The retained outer family and its common middle multiplicity obey the separate estimates
--   \[
--   Z e^{-N\delta_N/12}\le A,\qquad
--   B e^{-N\delta_N/8}\le 4X^2H.
--   \]
--
--   The two inequalities expose the two finite counting outputs of the first hash. Their deliberately generous fourth-root losses absorb the explicit Behrend density, collision deletion, and equal-fiber trimming. The common multiplicity remains the matrix-multiplication factor \(\langle H,H,H\rangle\); terms sharing a mode coordinate are not counted as independent summands.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--272: the 2N-th power, modulus M=4*binom(N,G)^2+1, Salem--Spencer hashing, deletion of shared X/Y blocks, the surviving outer Z-block family, and its common C-tensor multiplicity H; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_CW_q6_coupled_survivor
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open MME BigOperators Filter Topology
universe u

theorem mme_CW_q6_primary_hash_Ctensor_outer_middle_fibers
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
        (Zcount : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤
          (A : ℝ) ∧
        (middle : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
          4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by sorry
