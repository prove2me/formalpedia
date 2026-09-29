-- Prove2me | Theorems.Thm_mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
-- name    : mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:50:15.793558+00:00
-- url     : https://prove2.me/theorems/57425766-7d7a-4af6-8364-53cda4a74a27
-- title:
--   $\Phi_{1,3,4}$ fixed-mode exact-profile fiber cardinality
-- statement:
--   Fix an exact $\Phi_{1,3,4}$ profile address and one of its three mode words. The number of exact addresses with that same mode word is
--
--   $$
--   \prod_s\frac{m_{i,s}!}{\prod_{r:\,r_i=s} n_r!},
--   $$
--
--   where $n_r$ is the prescribed multiplicity of joint pattern $r$ and $m_{i,s}$ is its mode-$i$ marginal multiplicity. Here the eight joint patterns are $004,013,022,031,103,112,121,130$, with multiplicities $(\alpha,\beta,\gamma,\delta,\delta,\gamma,\beta,\alpha)$ and $\alpha+\beta+\gamma+\delta=N$.
--
--   For each fixed marginal symbol $s$, this is the multinomial number of ways to refine its coordinate fiber into the joint pattern classes lying above $s$. The product over $s$ is the sharp fixed-mode degree used by the cyclic hashing collision bound.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, multinomial type counts in Lemma 3.3 (pp. 359–361), specialized to the $\Phi_{1,3,4}$ profile of Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_profile_data

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_fixed_mode_exact_profile_fiber_card
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    (w : ExactProfileAddress N alpha beta gamma delta)
    (i : Fin 3) :
    Nat.card
        {v : ExactProfileAddress N alpha beta gamma delta //
          v.1.1 i = w.1.1 i} =
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial := by
  sorry
