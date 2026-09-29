-- Prove2me | Theorems.Thm_mme_type_cover_uniform_copy_extraction
-- name    : mme_type_cover_uniform_copy_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:40:10.463946+00:00
-- url     : https://prove2.me/theorems/cf891b07-9e9a-40d2-b0de-14b5045c2e97
-- title:
--   Keep all copies while reassembling a finite profile cover
-- statement:
--   Suppose a tensor T restricts from the direct sum of s profile pieces, and each piece can be extracted c times independently from a common source S. Then c independent copies of T restrict from s independent copies of S. Both multiplicities are exact, including zero cases; the type reconstruction consumes s source copies.
-- source:
--   Finite algebraic ingredients for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3, Theorem 6.4, and Sections 6.5–6.6. These statements retain explicit finite hole budgets and type-copy overheads; they do not assert the entropy asymptotics or numerical certificate.

import Theorems.Thm_mme_bigAdd_mono_restrict
import Definitions.Def_mme_rank_bridge

open MME MME.TensorObj BigOperators
universe u
set_option autoImplicit false

theorem mme_type_cover_uniform_copy_extraction {K : Type u} [Field K] {types copies : ℕ}
    (source target : TensorObj K 3) (piece : Fin types → TensorObj K 3)
    (hcover : Restrict target (bigAdd piece))
    (hextract : ∀ j, Restrict (bigAdd (fun _ : Fin copies ↦ piece j)) source) :
    Restrict (bigAdd (fun _ : Fin copies ↦ target))
      (bigAdd (fun _ : Fin types ↦ source)) := by sorry
