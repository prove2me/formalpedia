-- Prove2me | Definitions.Def_mme_stothers_phi134_cyclic_grading_address
-- name    : mme_stothers_phi134_cyclic_grading_address
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-05T10:13:56.282+00:00
-- url     : https://prove2.me/theorems/4ff2ab1d-43ac-4fad-bf32-c4f4490e7391
-- title:
--   Cyclic grading address of a phi_134 exact edge
-- statement:
--   Given three cyclic copies of an exact $\Phi_{1,3,4}$ profile, combine their three outer five-grades in the cyclic mode order to obtain the address in the $5^3$-class cyclic product grading. This is the literal grading word used by induced tensor zeroing after the hashing step.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Lemma 5.1(iii), pp. 359--365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data
import Definitions.Def_mme_cyclic_triple_grading

open MME

namespace MME.StothersFourth.Phi134

set_option autoImplicit false

def cyclicGradingAddress
    {N alpha beta gamma delta : ℕ}
    (e : CyclicExactEdge N alpha beta gamma delta)
    (i : Fin 3) (j : Fin (2 * N)) : Fin (5 * (5 * 5)) :=
  mmeCyclicTripleGrade
    (fun s ↦ e.1.1.1 s j)
    (fun s ↦ e.2.1.1.1 s j)
    (fun s ↦ e.2.2.1.1 s j) i

end MME.StothersFourth.Phi134


