-- Prove2me | Theorems.Thm_continuous_log_has_zero_lift_increment_on_closed_loop
-- name    : continuous_log_has_zero_lift_increment_on_closed_loop
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T02:14:12.654752+00:00
-- url     : https://prove2.me/theorems/653f90e1-495b-43e7-8909-7910d74b7dd9
-- title:
--   A continuous logarithm has zero lift increment on a closed loop
-- statement:
--   Let $W$ be a preconnected subset of a topological space, let $u,v\in W$, and let $q:W\to S$ be continuous with $q(u)=q(v)$. Suppose $F:S\to\mathbb C$ has a continuous logarithm $f$ on $S$, and $h:W\to\mathbb C$ is continuous with $e^{h(x)}=F(q(x))$ for all $x\in W$. Then $h(u)=h(v)$.
--
--   This expresses the vanishing of the exponential-lift increment around a closed loop whenever a single-valued logarithm exists on the domain.
-- source:
--   A standard consequence of uniqueness of lifts and the exponential definition of winding number; see Sections 14 and 15 of Mario Bonk, Complex Analysis, https://www.math.ucla.edu/~mbonk/complana.pdf . Supporting work for https://prove2.me/theorems/499509f0-5564-4ad2-b052-bdaa0fac6f2b .

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

open Set

theorem continuous_log_has_zero_lift_increment_on_closed_loop
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (W : Set X) (hW : IsPreconnected W) (S : Set Y)
    (u v : X) (hu : u ∈ W) (hv : v ∈ W)
    (q : X → Y) (F f : Y → ℂ) (h : X → ℂ)
    (hq : ContinuousOn q W) (hqS : MapsTo q W S)
    (hf : ContinuousOn f S) (hh : ContinuousOn h W)
    (hfe : EqOn (fun z => Complex.exp (f z)) F S)
    (hqh : EqOn (fun x => Complex.exp (h x)) (fun x => F (q x)) W)
    (hloop : q u = q v) : h u = h v := by sorry
