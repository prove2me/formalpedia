-- Prove2me | Theorems.Thm_SphericalGeometry_greatCirclePath_eq_of_eventuallyEq
-- name    : SphericalGeometry.greatCirclePath_eq_of_eventuallyEq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T00:52:21.233275+00:00
-- url     : https://prove2.me/theorems/d0f60e68-3b2a-482f-9aee-e59e724644e6
-- title:
--   A great circle is determined by an arbitrarily short arc
-- statement:
--   If two great circles
--
--   $$
--   c(t)=\cos(t)\,v_1+\sin(t)\,v_2,\qquad c'(t)=\cos(t)\,u_1+\sin(t)\,u_2
--   $$
--
--   agree on a neighbourhood of a single parameter, then $v_1=u_1$ and $v_2=u_2$, so they agree everywhere.
--
--   **Role.** This is the uniqueness of lifts, which is the hinge of the billiards argument. A closed billiards path in the model spherical chamber $\Delta_{\mathrm{mod}}=\mathbb S^{N-1}/W$ has many lifts to unit-speed geodesics of $\mathbb S^{N-1}$ — one for each choice of preimage of a single point — but *only one* for each such choice. That is what turns the closing relation $c(0)=c(\lambda)$ downstairs into the global equivariance $\bar c(s+\lambda)=w\cdot\bar c(s)$ upstairs for a single Weyl element $w$: the two curves $s\mapsto\bar c(s+\lambda)$ and $s\mapsto w\cdot\bar c(s)$ are both lifts and they agree at one parameter, hence everywhere. Without that step the period argument does not get off the ground.
--
--   The proof needs no orthonormality and no nondegeneracy: pairing the difference against an arbitrary vector $x$ turns the hypothesis into a first harmonic $\langle v_1-u_1,x\rangle\cos t+\langle v_2-u_2,x\rangle\sin t$ vanishing near $t_0$, whose coefficients must then vanish; taking $x=v_1-u_1$ and $x=v_2-u_2$ finishes it. In particular an arbitrarily short arc suffices, which is what the local nature of a billiards path requires.
-- source:
--   The lift-uniqueness step in the proof of Lemma 4.6 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608 ("while many such lifts exist, prescribing the value at one parameter completely determines the lifted map").

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

open Filter Topology

theorem greatCirclePath_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v1 v2 u1 u2 : E) (t0 : ℝ)
    (h : ∀ᶠ t in 𝓝 t0, greatCirclePath v1 v2 t = greatCirclePath u1 u2 t) :
    v1 = u1 ∧ v2 = u2 := by sorry

end SphericalGeometry
