-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_mode_word_tuple_injective
-- name    : mme_stothers_phi134_cyclic_mode_word_tuple_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:50:27.634712+00:00
-- url     : https://prove2.me/theorems/1d67a802-c15b-46ac-a4f2-f277769a2803
-- title:
--   $\Phi_{1,3,4}$ cyclic mode projections are injective
-- statement:
--   For the cyclic three-copy $\Phi_{1,3,4}$ profile family, the three vertex projections determine the underlying edge uniquely:
--
--   $$
--   \bigl(\forall i\in\{0,1,2\},\;v_i(e)=v_i(f)\bigr)\Longrightarrow e=f.
--   $$
--
--   Each original profile address contributes each of its three mode words exactly once among the cyclic projections. Hence the projection tuple loses no coordinate data. This injectivity is the edge-separation input for the collision bound.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, cyclic type construction in Lemma 3.3 (pp. 359–361), specialized to $\Phi_{1,3,4}$ in Lemma 5.1(iii) (p. 365); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_mode_word_tuple_injective :
    ∀ {N alpha beta gamma delta : ℕ},
      Function.Injective
        (cyclicModeWord (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) (delta := delta)) := by
  sorry
