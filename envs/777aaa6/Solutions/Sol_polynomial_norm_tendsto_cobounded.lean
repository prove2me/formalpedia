-- Prove2me | solution 1 for polynomial_norm_tendsto_cobounded
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:51:05.402531+00:00
-- url     : https://prove2.me/submissions/3ad989b7-ff7f-471f-8a3f-ba01a8144960

import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Basic

open Polynomial Filter Bornology

theorem solution {f : ℂ[X]} (hf : 0 < degree f) :
    Tendsto (fun z : ℂ => ‖f.eval z‖) (cobounded ℂ) atTop := by
  exact f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop

#print axioms solution
