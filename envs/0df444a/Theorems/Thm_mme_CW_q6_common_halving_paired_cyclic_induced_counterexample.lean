-- Prove2me | Theorems.Thm_mme_CW_q6_common_halving_paired_cyclic_induced_counterexample
-- name    : mme_CW_q6_common_halving_paired_cyclic_induced_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:26:26.619647+00:00
-- url     : https://prove2.me/theorems/411cb656-3d20-49c1-9f65-43ffc31567b2
-- title:
--   A common-halving primary family need not be paired-cyclic-induced
-- statement:
--   There is an exact coupled $q=6$ primary hash family at parameters $N=2$ and $L=G=1$, with two outer fibers and one entry per fiber, together with a single balanced halving shared by both entries, for which paired cyclic inducedness fails. Equivalently,
--
--   $$
--   	ext{ordinary primary inducedness}+	ext{common balanced halving};
--   otRightarrow;	ext{paired cyclic inducedness}.
--   $$
--
--   A non-diagonal triple survives simultaneously in the twice-cyclic first half and the once-cyclic second half. Hence the ordinary first-hash condition cannot by itself justify the paired 121/211 off-support vanishing step.
-- source:
--   Finite explicit counterexample obtained by auditing the paired cyclic mixed-support equations for the q=6 four-sum coupled constituent. The support convention is the one used in Coppersmith--Winograd (1990) and the 121/211 orientations in Duan--Wu--Zhou, arXiv:2210.10173v5, Section 6.3/Table 2.

import Definitions.Def_mme_CW_q6_paired_cyclic_induced

open MME

set_option autoImplicit false

theorem mme_CW_q6_common_halving_paired_cyclic_induced_counterexample :
    ∃ family : CWQ6PrimaryHashFamily 2 1 1 2 1,
      ∃ halving : family.CommonBalancedXYHalving,
        ¬ family.PairedCyclicInduced halving := by
  sorry
