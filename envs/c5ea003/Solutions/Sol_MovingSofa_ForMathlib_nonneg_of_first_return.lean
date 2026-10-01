-- Prove2me | solution 1 for MovingSofa.ForMathlib.nonneg_of_first_return
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T18:24:06.251248+00:00
-- url     : https://prove2.me/submissions/7d6856cc-320d-4b8e-a040-cb126d8cdd4e

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

theorem solution {g : ℝ → ℝ} {a t c d : ℝ} (hat : a < t)
    (hd : HasDerivAt g d t) (hgt : g t = c) (hleft : ∀ u ∈ Set.Ico a t, g u < c) :
    0 ≤ d := by
  have hIco : Set.Ico a t ∈ nhdsWithin t (Set.Iio t) := Ico_mem_nhdsLT hat
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono t (fun x hx => ne_of_lt hx) :
      nhdsWithin t (Set.Iio t) ≤ nhdsWithin t (Set.compl {t}))
  refine ge_of_tendsto hsl (Filter.eventually_of_mem hIco fun u hu => ?_)
  rw [slope_def_field, hgt]
  exact le_of_lt (div_pos_of_neg_of_neg (by linarith only [hleft u hu])
    (by linarith only [hu.2]))
