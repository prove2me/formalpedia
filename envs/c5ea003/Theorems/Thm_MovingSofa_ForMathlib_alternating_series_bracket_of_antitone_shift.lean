-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_alternating_series_bracket_of_antitone_shift
-- name    : MovingSofa.ForMathlib.alternating_series_bracket_of_antitone_shift
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:59:53.76768+00:00
-- url     : https://prove2.me/theorems/be8f6395-b402-420e-8376-c21ab1359b26
-- title:
--   Leibniz bracketing with shifted antitone tail
-- statement:
--   An alternating series antitone from an even index onward is bracketed by consecutive partial sums; the shifted Leibniz estimate.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/SpecificLimits/AlternatingBracket.lean#L40-L69

import Mathlib.Analysis.SpecificLimits.Normed
open scoped BigOperators

namespace MovingSofa
namespace ForMathlib

theorem alternating_series_bracket_of_antitone_shift {f : ℕ → ℝ} {l : ℝ} (N : ℕ)
    (hfl : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
      Filter.atTop (nhds l))
    (hfa : Antitone fun n ↦ f (2 * N + n)) :
    (∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * f i) ≤ l ∧
      l ≤ ∑ i ∈ Finset.range (2 * N + 1), (-1 : ℝ) ^ i * f i := by sorry

end ForMathlib
end MovingSofa
