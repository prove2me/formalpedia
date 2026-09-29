-- Prove2me | Definitions.Def_CTensorOneHOneCertificate
-- name    : CTensorOneHOneCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T01:49:43.413815+00:00
-- url     : https://prove2.me/theorems/7056d2e5-7ba1-421c-a2b9-872b6dfdbc57
-- title:
--   Finite C-tensor certificate over $\langle 1,H,1\rangle$
-- statement:
--   Let $T$ be an order-three tensor over a field. A `CTensorOneHOneCertificate` records that $T$ is a finite Strassen C-tensor over $\langle1,H,1\rangle$. It gives a grading with $H$ distinct grades in each of the first two modes and one common final grade in the third mode. The only supported coarse blocks are
--
--   $$
--   (h,h,*)\qquad(0\le h<H).
--   $$
--
--   For every $h$, the corresponding block is isomorphic to a concrete matrix-multiplication tensor $\langle m_h,n_h,p_h\rangle$, and all component volumes have one common value,
--
--   $$
--   m_hn_hp_h=v.
--   $$
--
--   Crucially, the definition does not posit a simultaneous identification of the shared third-mode fine coordinates across different components. This is the source-faithful distinction between a C-tensor and a literal tensor product by one common fine factor.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 271, paragraph beginning 'This is, in Strassen's terminology, a C-tensor over <1,H,1>'; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_rank_bridge

universe u

namespace MME

def cTensorOneHOneAddress (H : ℕ) (h : Fin H) : Fin 3 → Fin (H + 1)
  | ⟨0, _⟩ => Fin.castSucc h
  | ⟨1, _⟩ => Fin.castSucc h
  | ⟨2, _⟩ => Fin.last H

structure CTensorOneHOneCertificate
    {K : Type u} [Field K]
    (T : TensorObj K 3) (H volume : ℕ) where
  grading : T.TypeGrading (H + 1)
  supported : ∀ σ : Fin 3 → Fin (H + 1),
    σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
      grading.blockTensor σ = 0
  m : Fin H → ℕ
  n : Fin H → ℕ
  p : Fin H → ℕ
  component : ∀ h : Fin H,
    TensorObj.Isomorphic
      (MMObj K (m h) (n h) (p h))
      (grading.blockSubtensor (cTensorOneHOneAddress H h))
  common_volume : ∀ h : Fin H, m h * n h * p h = volume

end MME


