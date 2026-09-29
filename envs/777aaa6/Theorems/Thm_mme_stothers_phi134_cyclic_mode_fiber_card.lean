-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_mode_fiber_card
-- name    : mme_stothers_phi134_cyclic_mode_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:50:11.230942+00:00
-- url     : https://prove2.me/theorems/00330e5b-d6a4-4dc7-9257-c38e304f6190
-- title:
--   $\Phi_{1,3,4}$ uniform cyclic mode-fiber degree
-- statement:
--   For an exact cyclic $\Phi_{1,3,4}$ edge $e$, fix any one of its three cyclic vertices. Let
--
--   $$
--   D_t=\prod_s\frac{m_{t,s}!}{\prod_{r:\,r_t=s} n_r!}
--   $$
--
--   be the number of exact profile addresses sharing a prescribed mode-$t$ word. Then the number of cyclic exact edges sharing the chosen cyclic vertex with $e$ is independent of the chosen cyclic mode and equals
--
--   $$
--   D_0D_1D_2.
--   $$
--
--   Indeed, each cyclic vertex contains one mode word from each of the three independent profile-address copies, in a cyclic order. Its fiber is therefore the Cartesian product of the three fixed-mode fibers. This gives the sharp uniform degree parameter used in the Phi134 hashing and collision-pruning argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, multinomial type degrees in Lemma 3.3 (pp. 359–361), specialized to the cyclic $\Phi_{1,3,4}$ construction of Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_mode_fiber_card
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    (e : CyclicExactEdge N alpha beta gamma delta)
    (i : Fin 3) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    Nat.card
        {f : CyclicExactEdge N alpha beta gamma delta //
          cyclicModeWord f i = cyclicModeWord e i} =
      D 0 * (D 1 * D 2) := by
  sorry
