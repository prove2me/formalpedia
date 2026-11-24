-- Prove2me | Theorems.Thm_ZeroCount_count_le_of_parts
-- name    : ZeroCount.count_le_of_parts
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:23:58.501179+00:00
-- url     : https://prove2.me/theorems/04b5b171-38a8-490c-9089-0ea9eedba58c
-- title:
--   Turing band count bounds multiplicity sum of zeros in the box
-- statement:
--   Let $d$ be a Turing band $[T_0,T_1]$ with ball $B(c,R)$ and claimed count $n$, and $E$ rational enclosures of the five RvM edge argument changes, satisfying the sharp-pin side conditions `H11K.ValidS`, the cap geometry, zero-free clearance slabs $[T_0-\delta_0,T_0]$ and $[T_1,T_1+\delta_1]$, the K6 side bounds and the two horizontal enclosures. Then for every finite set $U$ of zeros $\rho$ of $\zeta$ with $0<\Re\rho<1$ and $T_0\le \Im\rho\le T_1$, $\sum_{\rho\in U}\operatorname{ord}_\rho\zeta \le n$.
-- source:
--   Broughan RH collection, Schoenfeld zero-count lemma (zerocount lane)

import Mathlib
import Definitions.Def_ArdaRH65K_Turing121_BandGlue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Seg
import Definitions.Def_ArdaRH65K_Turing121_H11K_Turing
import Definitions.Def_ArdaRH65K_Turing121_ArgChangeGlue
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore

theorem ZeroCount.count_le_of_parts {σ0 σ1 δ0 δ1 : ℝ} (d : BandGlue.BandData) (E : Arb4.EnclQ)
    (hV : H11K.ValidS σ0 σ1 (Arb4.withEncl d E))
    (hG : d.CapGeom δ0 δ1) (hs0 : EdgeClearGlue.SlabClear (d.T0 - δ0) d.T0)
    (hs1 : EdgeClearGlue.SlabClear d.T1 (d.T1 + δ1))
    (hS : ArgChangeGlue.K6Side (Arb4.withEncl d E))
    (hH1 : DiffractionCore.argChangeHoriz riemannZeta d.T1 2 (-1) ∈ Set.Icc E.L2.val E.H2.val)
    (hH0 : DiffractionCore.argChangeHoriz riemannZeta d.T0 2 (-1) ∈ Set.Icc E.L3.val E.H3.val)
    (U : Finset ℂ)
    (hU : ∀ ρ ∈ U, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ d.T0 ≤ ρ.im ∧ ρ.im ≤ d.T1) :
    ∑ ρ ∈ U, analyticOrderNatAt riemannZeta ρ ≤ d.n := by sorry
