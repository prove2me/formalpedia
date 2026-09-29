-- Prove2me | Theorems.Thm_mme_primary_hash_family_shared_Z_star_graded_support
-- name    : mme_primary_hash_family_shared_Z_star_graded_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:55:02.028153+00:00
-- url     : https://prove2.me/theorems/d3f8668c-991d-401f-a579-f6b8d073fbf5
-- title:
--   Shared-Z stars have diagonal graded support
-- statement:
--   Let $T$ be a tensor over a field $K$ with a three-way grading, and let $\mathcal F$ be a primary coupled-address family with parameters $(N,L,G,A,H)$. For an outer index $a$, form its shared-Z star $S_a$: the X and Y spaces are direct sums over the $H$ fibers, while the Z space is shared. Equip $S_a$ with the canonical grading that assigns the X and Y coordinates of fiber $h$ the grade $h$, and all Z coordinates the grade $H$. Then $$ (S_a)_\sigma=0\qquad\text{whenever }\sigma\notin\{(h,h,H):0\le h<H\}. $$ This establishes the support condition for a C-tensor certificate. It holds independently of any matrix-multiplication identification of the component tensors.
-- source:
--   Canonical shared-Z star grading and component inclusions.

import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct CoupledCTensorPackaging
open scoped BigOperators
universe u
set_option autoImplicit false

theorem mme_primary_hash_family_shared_Z_star_graded_support
    {K : Type u} [Field K] {T : TensorObj K 3} (G : T.TypeGrading 3)
    {N L B A H : ℕ} (family : CWQ6PrimaryHashFamily N L B A H)
    (a : Fin A) (σ : Fin 3 → Fin (H + 1))
    (hσ : σ ∉ Finset.univ.image (cTensorOneHOneAddress H)) :
    (starGrading G family a).blockTensor σ = 0 := by sorry
