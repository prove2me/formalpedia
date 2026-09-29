-- Prove2me | Definitions.Def_mme_cyclic_triple_grading
-- name    : mme_cyclic_triple_grading
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T23:23:43.064044+00:00
-- url     : https://prove2.me/theorems/f629ee65-7543-4d04-95f2-03607d0cb8b5
-- title:
--   Product grading for a cyclic tensor symmetrization
-- statement:
--   Let a three-mode tensor $T$ carry a finite grading with grade set $[t]$. On the cyclic symmetrization $T\otimes\pi T\otimes\pi^2T$, this module forms the product grading whose mode-$i$ label is the ordered triple of the grade in $T$, the grade in $\pi T$ pulled back by $\pi^{-1}$, and the grade in $\pi^2T$ pulled back by $\pi^{-2}$. The three labels are encoded in a single set of size $t^3$.
--
--   This is the grading interface needed to apply the laser method simultaneously to the three cyclic copies of a constituent while retaining exact control of each factor block.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), cyclic symmetrization and constituent extraction in Lemma 5.1, pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The product-grading construction is standard tensor-product linear algebra.

import Definitions.Def_mme_TypeGrading_permutation
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_cyclicSymmetrization_public_perm

open MME TensorObj.TypeGrading

universe u

namespace MME

set_option autoImplicit false

noncomputable def mmeGradingOfEq
    {K : Type u} [Field K] {d t : Nat}
    {A B : TensorObj K d} (h : A = B)
    (G : B.TypeGrading t) : A.TypeGrading t :=
  h.symm ▸ G

noncomputable def mmePublicCyclicTripleGrading
    {K : Type u} [Field K] {T : TensorObj K 3} {t : Nat}
    (G : T.TypeGrading t) :
    (TensorObj.kron T
      (TensorObj.kron
        (TensorObj.permObj cyclicPerm T)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T))).TypeGrading
      (t * (t * t)) :=
  kronGrading G
    (kronGrading
      (permObjGrading G cyclicPerm)
      (permObjGrading G (cyclicPerm.trans cyclicPerm)))

noncomputable def mmeCyclicTripleGrading
    {K : Type u} [Field K] {T : TensorObj K 3} {t : Nat}
    (G : T.TypeGrading t) :
    (cyclicSymmetrization T).TypeGrading (t * (t * t)) :=
  mmeGradingOfEq (cyclicSymmetrization_eq_public_perm T)
    (mmePublicCyclicTripleGrading G)

def mmeCyclicTripleGrade
    {t : Nat} (rhoX rhoY rhoZ : Fin 3 -> Fin t) (i : Fin 3) :
    Fin (t * (t * t)) :=
  finProdFinEquiv
    (rhoX i,
      finProdFinEquiv
        (rhoY (cyclicPerm.symm i),
          rhoZ ((cyclicPerm.trans cyclicPerm).symm i)))

end MME


