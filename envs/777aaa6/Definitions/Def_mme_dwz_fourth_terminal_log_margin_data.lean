-- Prove2me | Definitions.Def_mme_dwz_fourth_terminal_log_margin_data
-- name    : mme_dwz_fourth_terminal_log_margin_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T18:58:33.490059+00:00
-- url     : https://prove2.me/theorems/32b24f26-34fa-49a5-abdd-9e6bd4453e96
-- title:
--   Definitions for mme_dwz_fourth_terminal_log_margin
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_terminal_log_margin, from the exact fourth-power scalar assembly of Duan-Wu-Zhou.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Mathlib.Tactic
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate

open BigOperators Finset

set_option autoImplicit false

namespace MME.DWZFourthScalar

def reciprocalFiveT : ℚ := 3 / 13

def reciprocalFiveLogLower : ℚ :=
  2 * ∑ i ∈ range 6,
      reciprocalFiveT ^ (2 * i + 1) / (2 * i + 1) -
    3 * (69314718057 / 100000000000 : ℚ)

def reciprocalFiveLogUpper : ℚ :=
  2 * ((∑ i ∈ range 6,
      reciprocalFiveT ^ (2 * i + 1) / (2 * i + 1)) +
      reciprocalFiveT ^ 13 / (1 - reciprocalFiveT ^ 2)) -
    3 * (69314718055 / 100000000000 : ℚ)

def logFiveLower : ℚ := -reciprocalFiveLogUpper

def reciprocalTargetT : ℚ := 169499 / 649701

def reciprocalTargetLogLower : ℚ :=
  2 * ∑ i ∈ range 6,
      reciprocalTargetT ^ (2 * i + 1) / (2 * i + 1) -
    12 * (69314718057 / 100000000000 : ℚ)

def reciprocalTargetLogUpper : ℚ :=
  2 * ((∑ i ∈ range 6,
      reciprocalTargetT ^ (2 * i + 1) / (2 * i + 1)) +
      reciprocalTargetT ^ 13 / (1 - reciprocalTargetT ^ 2)) -
    12 * (69314718055 / 100000000000 : ℚ)

def targetLogUpper : ℚ := -reciprocalTargetLogLower

def naturalRateFloor : ℚ := 155673 / 20000

end MME.DWZFourthScalar


