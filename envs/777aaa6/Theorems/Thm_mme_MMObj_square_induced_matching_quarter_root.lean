-- Prove2me | Theorems.Thm_mme_MMObj_square_induced_matching_quarter_root
-- name    : mme_MMObj_square_induced_matching_quarter_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:14:29.982983+00:00
-- url     : https://prove2.me/theorems/164c1c01-c1c7-459a-a029-1c2046e93201
-- title:
--   A uniform H^{2-o(1)} induced matching in square matrix multiplication
-- statement:
--   Fix a field \(K\).  For every sufficiently large \(N\), uniformly for each integer \(H\) with \(0<H\le4^N\), the square matrix-multiplication tensor \(\langle H,H,H\rangle\) has a coordinate restriction to a direct sum of \(k\) scalar multiplications such that
--   \[
--   H^2\exp\!\left(-N(N+1)^{-1/4}\right)\le k.
--   \]
--
--   Equivalently, the support of \(\langle H,H,H\rangle\) contains a quantitatively large induced matching.  The fourth-root loss is intentionally generous: the explicit Behrend density gives an \(\exp(-O(\sqrt{\log H}))\) loss, which is uniformly absorbed because \(\log H\le N\log4\).  The conclusion is \(H^{2-o(1)}\); it does not assert the generally false exact restriction to \(H^2\) independent scalar tensors.
-- source:
--   The Salem--Spencer induced-matching step used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), including the C-tensor/value argument surrounding journal pp. 264 and 270--272; https://www.sciencedirect.com/science/article/pii/S0747717108800132. The finite density input is the explicit Behrend theorem mme_behrend_explicit_threeAP_free (Prove2Me cb45e6ba-b86a-4119-a08e-f162c8fbc86b).

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_tensor_rank
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open MME BigOperators Filter Topology
universe u

theorem mme_MMObj_square_induced_matching_quarter_root
    {K : Type u} [Field K] :
    ∀ᶠ N : ℕ in atTop,
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      ∀ H : ℕ, 0 < H → H ≤ 4 ^ N →
        ∃ k : ℕ,
          TensorObj.Restrict
            (TensorObj.bigAdd (fun _ : Fin k => MMObj K 1 1 1))
            (MMObj K H H H) ∧
          ((H : ℝ) ^ 2) * Real.exp (-((N : ℝ) * loss)) ≤ (k : ℝ) := by sorry
