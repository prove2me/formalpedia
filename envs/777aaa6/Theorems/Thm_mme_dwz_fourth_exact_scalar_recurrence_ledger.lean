-- Prove2me | Theorems.Thm_mme_dwz_fourth_exact_scalar_recurrence_ledger
-- name    : mme_dwz_fourth_exact_scalar_recurrence_ledger
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T14:58:37.411282+00:00
-- url     : https://prove2.me/theorems/3784d75b-d5d5-4ea2-8755-0711d8802e65
-- title:
--   The 181-node exact scalar ledger passes its own recurrence check
-- statement:
--   The recursive value construction for the fourth power of $\mathrm{CW}_5$ is summarized by a scalar ledger of 181 nodes. Node $i$ records a list of children — each a pair (earlier index, non-negative rational coefficient) — a **retained floor** $F_i$, and a **rate floor** $P_i$, all exact rationals. The ledger is *accepted* when every node satisfies its own recurrence against the rate floors of the nodes before it:
--
--   $$\text{all coefficients} \ge 0, \qquad P_i \;\le\; F_i \;+\; \sum_{(j, c) \in \mathrm{children}(i)} c \cdot P_j .$$
--
--   `checkLedger` runs exactly this test, left to right, starting from the empty prior array, so each node is checked against already-established floors only.
--
--   This theorem asserts two things:
--
--   1. `checkLedger = true` — every one of the 181 nodes passes, by kernel evaluation of the exact rational arithmetic;
--   2. $155673/20000 \le 7783662026649/10^{12}$ — the ledger's final rate floor is at least the stated comparator.
--
--   Together they say that the recursion's arithmetic is internally consistent and reaches the claimed floor. Nothing here is a tensor statement: the ledger records rates that other theorems must realize, node by node. Its role is to isolate all the numerical bookkeeping of the construction into a single machine-checkable certificate, verified by the kernel rather than by compiled evaluation.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_exact_scalar_ledger_data

open MME.DWZFourthScalarLedger

set_option autoImplicit false

theorem mme_dwz_fourth_exact_scalar_recurrence_ledger :
    checkLedger = true /\ naturalRateFloor <= finalRateFloor := by sorry
