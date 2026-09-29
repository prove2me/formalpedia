-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_supported_mix_closure
-- name    : mme_stothers_phi134_cyclic_supported_mix_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:50:14.966632+00:00
-- url     : https://prove2.me/theorems/891415b9-b1fc-475c-b93e-daf750d8265c
-- title:
--   $\Phi_{1,3,4}$ supported cyclic mixtures remain exact
-- statement:
--   Let $x,y,z$ be three exact cyclic $\Phi_{1,3,4}$ edges. Suppose the three cyclic mixtures obtained by taking mode zero from one address, mode one from the next, and mode two from the last are coordinatewise supported on the eight patterns $004,013,022,031,103,112,121,130$. Then there is an exact cyclic edge $e$ whose three vertices are respectively the mode-$0$ vertex of $x$, the mode-$1$ vertex of $y$, and the mode-$2$ vertex of $z$:
--
--   $$
--   v_0(e)=v_0(x),\qquad v_1(e)=v_1(y),\qquad v_2(e)=v_2(z).
--   $$
--
--   The prescribed Phi134 marginals are invariant under these modewise mixtures, and for this eight-pattern family the marginals uniquely force the exact joint profile. Thus each supported mixed address returns to the exact family. This is precisely the ambient-closure condition needed by type-2 isolation.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, type-2 cyclic compatibility in Lemma 3.3 (pp. 359–361) and the $\Phi_{1,3,4}$ profile in Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_supported_mix_closure
    {N alpha beta gamma delta : ℕ}
    (x y z : CyclicExactEdge N alpha beta gamma delta)
    (hsupport : CyclicCoordinatewiseSupported x y z) :
    ∃ e : CyclicExactEdge N alpha beta gamma delta,
      cyclicModeWord e 0 = cyclicModeWord x 0 ∧
      cyclicModeWord e 1 = cyclicModeWord y 1 ∧
      cyclicModeWord e 2 = cyclicModeWord z 2 := by
  sorry
