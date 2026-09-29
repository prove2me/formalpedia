-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_affine_hash_AP
-- name    : mme_stothers_phi134_cyclic_affine_hash_AP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:46:07.664217+00:00
-- url     : https://prove2.me/theorems/714e1575-1766-4e5e-be48-b047457fda96
-- title:
--   $\Phi_{1,3,4}$ cyclic affine hashes form an arithmetic progression
-- statement:
--   Let $x,y,z$ be three exact cyclic $\Phi_{1,3,4}$ edges whose three modewise mixtures are coordinatewise supported by the eight fourth-power source patterns. For every coefficient word $w$, shift $s$, offset $t$, and modulus $p$, their cyclic affine labels form a three-term arithmetic progression:
--
--   $$
--   H_0(x)+H_1(y)=2H_2(z)\qquad\text{in }\mathbb Z/p\mathbb Z.
--   $$
--
--   At every tensor-power coordinate, each supported pattern has three grades summing to $4$. The coefficient choices in the cyclic hash convert these three grade-sum identities into the displayed progression identity after summation. This is the algebraic invariant that lets a progression-free label set force equal labels.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, Lemma 3.3 (pp. 359–361) and its $\Phi_{1,3,4}$ specialization in Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_affine_hash_AP
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p)
    (x y z : CyclicExactEdge N alpha beta gamma delta)
    (hsupp : CyclicCoordinatewiseSupported x y z) :
    cyclicAffineHash p N alpha beta gamma delta w shift offset 0 x +
        cyclicAffineHash p N alpha beta gamma delta w shift offset 1 y =
      2 * cyclicAffineHash p N alpha beta gamma delta w shift offset 2 z := by
  sorry
