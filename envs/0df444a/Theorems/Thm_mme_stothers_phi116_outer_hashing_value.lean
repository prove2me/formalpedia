-- Prove2me | Theorems.Thm_mme_stothers_phi116_outer_hashing_value
-- name    : mme_stothers_phi116_outer_hashing_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:37:08.228504+00:00
-- url     : https://prove2.me/theorems/f66ea222-a794-411b-a790-dc66cdf61c0a
-- title:
--   Davie--Stothers phi_116: outer hashing and optimized cyclic value
-- statement:
--   Let $\varphi_{116}$ carry the literal outer three-grading. Assume its support is contained in the four addresses $(000),(111),(012),(102)$, its $(012)$ and $(102)$ blocks restrict to $\langle12,1,12\rangle$, and its $(000)$ and $(111)$ blocks restrict to the coupled constituent $D_6$. For $2\le3\tau\le3$, every fixed nonnegative base
--
--   $$
--   V<4\left(E(\tau)^2+2L(\tau)\right),\qquad E(\tau)=12^{3\tau},\quad L(\tau)=4\,6^{3\tau}(6^{3\tau}+2),
--   $$
--
--   is attained by the tau-value of the cyclic symmetrization of $\varphi_{116}$.
--
--   This isolates the remaining Salem--Spencer extraction, recursive coupled substitution, two-type optimization, and cofinal limiting argument in Lemma 5.1(i). The structural hypotheses refer to one grading of the literal source tensor, preventing an external-direct-sum surrogate.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_outer_grading
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tensor_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_outer_hashing_value
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (hsupport :
      ∀ sigma : Fin 3 → Fin 3,
        sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
        sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
        (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockTensor sigma = 0)
    (hcomponents :
      TensorObj.Restrict (MMObj K 12 1 12)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![0, 1, 2]) ∧
        TensorObj.Restrict (MMObj K 12 1 12)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![1, 0, 2]) ∧
        TensorObj.Restrict (coupledObj K 6)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![0, 0, 0]) ∧
        TensorObj.Restrict (coupledObj K 6)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![1, 1, 1])) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 5 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V := by
  sorry
