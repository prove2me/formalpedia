-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_primary_hash_Ctensor_quarter_root
-- name    : mme_CW_q6_coupled_primary_hash_Ctensor_quarter_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:14:32.676541+00:00
-- url     : https://prove2.me/theorems/4ed970ee-06fa-49ec-9191-df8aabef5f9a
-- title:
--   Primary coupled q=6 hashing with the shared-index C-tensor retained
-- statement:
--   Fix a field \(K\) and \(\tau\) with \(3\tau\ge2\).  Put
--   \[
--   L=\left\lfloor\frac{2N}{6^{3\tau}+2}\right\rfloor,\qquad
--   G=N-L,\qquad s=36^{2G}6^{2L},
--   \]
--   and assume \(L>0\), \(L+G=N\), and \(341L<100G\).  For all sufficiently large \(N\), the first Salem--Spencer hashing and equal-fiber pruning in the coupled \(q=6\) construction produce positive integers \(A,H\), with \(H\le4^N\), and an actual coordinate restriction to \(A^3\) macro blocks
--   \[
--   \bigoplus_{a=1}^{A^3}\left(\langle H,H,H\rangle\otimes S_{L,G}\right).
--   \]
--   Writing \(R=4\,6^{3\tau}(6^{3\tau}+2)\) and \(\delta_N=(N+1)^{-1/4}\), these parameters satisfy
--   \[
--   \bigl(R e^{-\delta_N/2}\bigr)^{2N}
--    \le A^3H^2\,(s^3)^\tau.
--   \]
--
--   The factor \(\langle H,H,H\rangle\) is deliberately retained as a matrix-multiplication tensor.  Thus middle-index terms which share coordinates, including a shared \(Z\)-block in one C-tensor orientation, are not asserted to be a direct sum.  This theorem isolates the first Behrend loss and the coarse C-tensor extraction; a separate induced-matching theorem is required before the \(H^2\) factor can be converted into independent survivors.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--272 (PDF pp. 20--22), especially the 2N-th power, the L/G profile, Salem--Spencer hashing, equal-fiber pruning, and the C-tensor over <1,H,1>; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_q6_coupled_survivor
open MME BigOperators Filter Topology
universe u

theorem mme_CW_q6_coupled_primary_hash_Ctensor_quarter_root
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
      let raw : ℝ :=
        4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
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
        (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
          (((A ^ 3 : ℕ) : ℝ) * ((H : ℝ) ^ 2)) *
            (((side * side * side : ℕ) : ℝ) ^ tau) := by sorry
