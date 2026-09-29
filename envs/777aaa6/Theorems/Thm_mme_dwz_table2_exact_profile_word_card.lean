-- Prove2me | Theorems.Thm_mme_dwz_table2_exact_profile_word_card
-- name    : mme_dwz_table2_exact_profile_word_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T20:50:33.8896+00:00
-- url     : https://prove2.me/theorems/64c7aecd-2108-4f39-8284-47ebda6d8375
-- title:
--   Exact Table-2 joint-profile words have multinomial cardinality
-- statement:
--   For every scaling parameter $m$, let $c_s=m\,\mathrm{component}(s)$ be the prescribed multiplicity of the fifteenth Table-2 component $s$. The number of source words of length $L=m\,\mathrm{scale}$ whose exact joint histogram is $(c_s)_{s\in[15]}$ is the multinomial coefficient
--
--   $$\#\{w:[L]\to[15]: |w^{-1}(s)|=c_s\text{ for every }s\}=\binom{L}{(c_s)_{s\in[15]}}.$$
--
--   This exact joint-profile count is the target cardinal retained by the global first hash; retaining only marginal histograms would be insufficient.
-- source:
--   Duan--Wu--Zhou Table-2 type enumeration; finite multinomial counting.

import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Set.Card

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_exact_profile_word_card (m : ℕ) :
    (Finset.univ.filter fun w :
        Fin (MME.DWZTable2Counts.scale * m) → Fin 15 ↦
          ∀ s, Fintype.card {t // w t = s} =
            MME.DWZTable2Counts.component s * m).card =
      Nat.multinomial Finset.univ
        (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) := by
  sorry
