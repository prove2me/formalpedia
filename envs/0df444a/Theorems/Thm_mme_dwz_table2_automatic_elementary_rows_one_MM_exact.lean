-- Prove2me | Theorems.Thm_mme_dwz_table2_automatic_elementary_rows_one_MM_exact
-- name    : mme_dwz_table2_automatic_elementary_rows_one_MM_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T20:55:53.968419+00:00
-- url     : https://prove2.me/theorems/7d38510f-46f4-4ca2-952b-1b4cd03dd2db
-- title:
--   Exact one-product extraction for the forced-profile elementary Table-2 rows
-- statement:
--   Fix a field $K$, a real exponent $\tau$, a scale $m$, and one of the Table-2 rows $s\in\{0,1,2,6,8,11\}$. Then the available-$Z$-word projection of the prescribed component power contains a rectangular matrix-multiplication tensor $\langle a,b,c\rangle$ whose six-copy weighted volume attains the exact row contribution with no asymptotic loss:
--
--   $$
--   B_s(\tau)^{6n_s(m)}\le \bigl((abc)^6\bigr)^\tau.
--   $$
--
--   For these rows the fine $Z$-profile is forced by the coarse grade: rows $1,2,6,8,11$ have only left grade $0$, while row $0$ has only left grade $2$. Consequently every canonical $Z$ word is available, so the proof may iterate the already-proved scalar, rectangular, and central-$220$ restrictions without discarding any coordinates.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 and Table 2, arXiv:2210.10173v5; forced-profile elementary component rows.

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection

open MME
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_table2_automatic_elementary_rows_one_MM_exact
    {K : Type u} [Field K] (tau : ℝ)
    (m : ℕ) (s : Fin 15)
    (hs : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 6 ∨ s = 8 ∨ s = 11) :
    ∃ a b c : ℕ,
      TensorObj.Restrict (MMObj K a b c)
        (restrictedComponentPower K s m) ∧
      (((componentBase tau s) ^
          (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
          Real.exp (-(0 : ℝ) * Real.sqrt
            (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
        (((((a * b * c) ^ 2) * ((a * b * c) ^ 2) *
              ((a * b * c) ^ 2) : ℕ) : ℝ) ^ tau) := by
  sorry
