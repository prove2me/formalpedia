-- Prove2me | solution 1 for BookSixth.latin_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T17:06:58.887065+00:00
-- url     : https://prove2.me/submissions/dcf1b8e2-d6d3-4899-9a27-1e1d2c850eb5

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_latin_bounds
import Theorems.Thm_BookSixth_latin_asymptotic_of_bounds

open scoped BigOperators
open BookSixth

theorem solution :
    Filter.Tendsto (fun n : ℕ => (latinCount n : ℝ) ^ (1 / (n : ℝ)^2) / (n : ℝ))
      Filter.atTop (nhds (Real.exp (-2))) := by
  exact BookSixth.latin_asymptotic_of_bounds
    (fun n hn => (BookSixth.latin_bounds n hn).1)
    (fun n hn => (BookSixth.latin_bounds n hn).2)
