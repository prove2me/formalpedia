-- Prove2me | Theorems.Thm_mme_stothers_phi134_hash_degree_bound
-- name    : mme_stothers_phi134_hash_degree_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:18:59.061285+00:00
-- url     : https://prove2.me/theorems/741b2255-a15e-428c-a8a1-744e85fefa6c
-- title:
--   $\Phi_{1,3,4}$ sharp cyclic hash-degree bound
-- statement:
--   Let $E$ be the exact cyclic $\Phi_{1,3,4}$ family and put $D_t=\prod_s m_{t,s}!/\prod_{r:r_t=s}n_r!$. For every mode $i$ and $e\in E$, the same-vertex fiber in $E$ has cardinality at most $D_0D_1D_2$. In fact the cyclic fiber theorem gives equality. This is the sharp finset degree bound used by the collision budget.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), Lemma 3.3 (pp. 359–361), specialized to $\Phi_{1,3,4}$ in Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

noncomputable section

theorem mme_stothers_phi134_hash_degree_bound
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    [DecidableEq (CyclicModeWord N)] :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    ∀ i : Fin 3,
      ∀ e ∈ edgeFinset N alpha beta gamma delta,
        ((edgeFinset N alpha beta gamma delta).filter
          (fun f ↦ cyclicModeWord f i = cyclicModeWord e i)).card ≤
            D 0 * (D 1 * D 2) := by
  sorry
