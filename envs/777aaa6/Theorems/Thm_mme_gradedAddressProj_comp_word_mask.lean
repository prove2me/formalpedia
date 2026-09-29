-- Prove2me | Theorems.Thm_mme_gradedAddressProj_comp_word_mask
-- name    : mme_gradedAddressProj_comp_word_mask
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:45:36.100794+00:00
-- url     : https://prove2.me/theorems/1bf2d14b-24fa-4159-b9f9-7fbc96546bd7
-- title:
--   Address projections survive word filters that retain matching grades
-- statement:
--   Let $T$ be a three-mode tensor with a finite grading, and choose a basis of one mode whose vectors project to zero in every incorrect grade. Fix an address of length $n$ and a predicate on basis words. Suppose every word whose grades match the address is retained by the predicate. If $P$ is the address projection and $M$ is the diagonal word mask, then $$P\circ M=P.$$ Thus an address projection can be applied after a word filter without change whenever the filter retains the address's matching words.
-- source:
--   Primary hash family inducedness and graded address projections.

import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch

open MME MME.DWZComponentRestriction Module
universe u
set_option autoImplicit false

theorem mme_gradedAddressProj_comp_word_mask
    {K : Type u} [Field K] {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (i : Fin 3) {ι : Type u}
    (b : Basis ι K (T.V i)) (grade : ι → Fin t)
    (hzero : ∀ (a : Fin t) (j : ι), grade j ≠ a → G.blockProj i a (b j) = 0)
    (address : Fin 3 → Fin N → Fin t)
    (keep : PowIndex ι N → Prop) [DecidablePred keep]
    (hkeep : ∀ w, (∀ r, grade (PowIndex.get N w r) = address i r) → keep w) :
    (gradedAddressProj G N address i).comp
        ((kronPowModeBasis T i b N).constr K
          (fun w => if keep w then kronPowModeBasis T i b N w else 0)) =
      gradedAddressProj G N address i := by sorry
