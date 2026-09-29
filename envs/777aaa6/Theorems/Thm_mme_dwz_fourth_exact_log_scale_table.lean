-- Prove2me | Theorems.Thm_mme_dwz_fourth_exact_log_scale_table
-- name    : mme_dwz_fourth_exact_log_scale_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T17:54:29.152985+00:00
-- url     : https://prove2.me/theorems/379e2598-d741-4c74-bc02-ff11f023bdc7
-- title:
--   Every entry of the q=5 logarithm scale table is admissible and its logarithm is bracketed
-- statement:
--   The scalar bookkeeping of the $q=5$ fourth-power construction needs the natural logarithm of several hundred exact rationals, at accuracy far beyond floating point. They are collected in one table: each entry is a pair $(q_i, k_i)$ of a positive rational and a scale, stored in thirty-one chunks and concatenated.
--
--   This theorem states the two facts that make the table usable:
--
--   1. **Every entry is admissible:** $0 < q_i$ and $1 \le q_i\,2^{k_i}$, so the scaled argument lies in the region where the series certificate applies.
--   2. **Every entry's logarithm is bracketed:** with six series terms,
--
--   $$\mathrm{autoScaledLogLower}(q_i, k_i, 6) \;\le\; \log q_i \;\le\; \mathrm{autoScaledLogUpper}(q_i, k_i, 6),$$
--
--   where the two endpoints are the computed rational bounds of the companion auto-scaled logarithm interval.
--
--   Both are established by kernel evaluation of the exact rational arithmetic — chunk by chunk for the admissibility test, and then by the interval theorem applied entry by entry. Nothing here depends on compiled evaluation or on floating-point estimates: the endpoints are rational functions of $q_i$, $k_i$ and the term count, and the kernel checks the inequalities that justify them.
--
--   The table's role is to let every entropy and rate computation downstream replace a transcendental logarithm by a pair of exact rationals.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_log_scale_table_data
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational

open MME.DWZFourthLogScaleTable

set_option autoImplicit false

theorem mme_dwz_fourth_exact_log_scale_table :
    (forall i : Fin entries.size,
      0 < argument i /\ 1 <= argument i * 2 ^ scale i) /\
    forall i : Fin entries.size,
      (MME.autoScaledLogLower (argument i) (scale i) 6 : Real) <=
          Real.log (argument i : Real) /\
        Real.log (argument i : Real) <=
          (MME.autoScaledLogUpper (argument i) (scale i) 6 : Real) := by sorry
