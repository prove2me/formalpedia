-- Prove2me | Theorems.Thm_mme_stothers_phi116_four_term_projection_zero
-- name    : mme_stothers_phi116_four_term_projection_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:22:02.454114+00:00
-- url     : https://prove2.me/theorems/77052685-5c63-4e53-a948-c7a8588aafbe
-- title:
--   Unsupported phi_116 outer projection kills every canonical four-term monomial
-- statement:
--   For any ordered four-tuple of canonical $CW_6$ monomials, first project to the coarse $(1,1,6)$ constituent and then to an outer $\varphi_{116}$ address. If that address is different from $000,111,012,$ and $102$, the projected rank-one term is zero. This is the literal termwise support calculation; summing it over the finite fourth-power expansion yields the exact four-edge block support.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21 and its proof, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_term_expansion

open MME TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_four_term_projection_zero
    (K : Type u) [Field K] (sigma : Fin 3 → Fin 3)
    (h000 : sigma ≠ ![0, 0, 0])
    (h111 : sigma ≠ ![1, 1, 1])
    (h012 : sigma ≠ ![0, 1, 2])
    (h102 : sigma ≠ ![1, 0, 2])
    (t₁ t₂ t₃ t₄ : MME.StothersFourth.Phi116.CWTerm 6) :
    PiTensorProduct.map
        (fun s =>
          (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockProj
            s (sigma s))
        (PiTensorProduct.map
          (fun s =>
            (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockProj s
              (MME.StothersFourth.Phi116.phi116ModeTotalGrade s))
          (interchange
            (interchange
              (MME.StothersFourth.Phi116.cwTermMonom K 6 t₁)
              (MME.StothersFourth.Phi116.cwTermMonom K 6 t₂))
            (interchange
              (MME.StothersFourth.Phi116.cwTermMonom K 6 t₃)
              (MME.StothersFourth.Phi116.cwTermMonom K 6 t₄)))) = 0 := by
  sorry
