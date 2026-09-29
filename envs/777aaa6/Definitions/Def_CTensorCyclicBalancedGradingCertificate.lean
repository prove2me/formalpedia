-- Prove2me | Definitions.Def_CTensorCyclicBalancedGradingCertificate
-- name    : CTensorCyclicBalancedGradingCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T02:53:48.442293+00:00
-- url     : https://prove2.me/theorems/ddc9ce9e-07d0-4c6d-89e3-2cf568747909
-- title:
--   Cyclic balanced grading data for a finite C-tensor
-- statement:
--   For a finite C-tensor $T$ over $\langle1,H,1\rangle$, a cyclic balanced grading certificate packages the exact finite data needed after passing to $T\otimes\pi T\otimes\pi^2T$. Its addresses are indexed by triples $(x,y,z)$ of balanced words. Their three mode coordinates depend on the pairs $(x,z)$, $(x,y)$, and $(y,z)$. The `mixed_support` field states the corresponding support law: a coordinatewise nonzero mixed block forces the three shared-word equalities. Each complete address block is isomorphic to a concrete matrix-multiplication tensor, and every such block has common volume $v^{3Hm}$.
--
--   The structure separates cyclic grading transport and block identification from induced-matching selection. Once this certificate exists, the generic induced-address zeroing theorem can perform all subsequent pruning.
-- source:
--   V. Strassen's C-tensor method as used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_CW_coupled_value

open MME

universe u

namespace MME

structure CTensorCyclicBalancedGradingCertificate
    {K : Type u} [Field K]
    (T : TensorObj K 3) (H volume m W : ℕ) where
  t : ℕ
  grading : (cyclicSymmetrization T).TypeGrading t
  address :
    (Fin W × Fin W × Fin W) → Fin 3 → Fin (H * m) → Fin t
  a : (Fin W × Fin W × Fin W) → ℕ
  b : (Fin W × Fin W × Fin W) → ℕ
  c : (Fin W × Fin W × Fin W) → ℕ
  mixed_support :
    ∀ es : Fin 3 → (Fin W × Fin W × Fin W),
      (∀ r : Fin (H * m),
        grading.blockTensor (fun i ↦ address (es i) i r) ≠ 0) →
      (es 1).2.1 = (es 2).2.1 ∧
      (es 2).2.2 = (es 0).2.2 ∧
      (es 0).1 = (es 1).1
  component : ∀ e,
    TensorObj.Isomorphic
      (MMObj K (a e) (b e) (c e))
      (gradedAddressBlock grading (address e))
  common_volume : ∀ e,
    a e * b e * c e = volume ^ (3 * (H * m))

end MME


