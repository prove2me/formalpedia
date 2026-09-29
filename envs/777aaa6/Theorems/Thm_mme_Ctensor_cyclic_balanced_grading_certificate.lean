-- Prove2me | Theorems.Thm_mme_Ctensor_cyclic_balanced_grading_certificate
-- name    : mme_Ctensor_cyclic_balanced_grading_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:54:19.490891+00:00
-- url     : https://prove2.me/theorems/6a22172c-fb6a-4c9b-938d-124f81aae256
-- title:
--   A finite C-tensor induces its cyclic balanced grading certificate
-- statement:
--   Let $T$ be a finite C-tensor over $\langle1,H,1\rangle$, with $H>0$ components of common volume $v$. Fix a balanced multiplicity $m$, and enumerate by $[W]$ the length-$Hm$ words in which every component label appears exactly $m$ times. Then the cyclic tensor
--
--   $$
--   T\otimes\pi T\otimes\pi^2T
--   $$
--
--   admits a cyclic balanced grading certificate. In particular, triples of balanced words give pair-addressed blocks, mixed nonzero blocks obey the matrix-multiplication support equalities, and every complete block is a matrix-multiplication tensor of volume $v^{3Hm}$.
--
--   This theorem is the structural grading-transport step in the C-tensor method. It contains neither a progression-free-set estimate nor an induced-matching choice; those are handled by generic downstream zeroing.
-- source:
--   V. Strassen's C-tensor method as used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_CTensorCyclicBalancedGradingCertificate

open MME

universe u

theorem mme_Ctensor_cyclic_balanced_grading_certificate
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (hH : 0 < H) (m W : ℕ)
    (words : Fin W ≃
      {w : Fin (H * m) → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}) :
    Nonempty (CTensorCyclicBalancedGradingCertificate T H volume m W) := by
  sorry
