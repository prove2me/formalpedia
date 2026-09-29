-- Prove2me | Theorems.Thm_bousquet_cgf_le_phi_via_herbst
-- name    : bousquet_cgf_le_phi_via_herbst
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-24T02:22:57.408326+00:00
-- url     : https://prove2.me/theorems/8e954c98-c11f-4f58-9b7b-da8e93005734
-- title:
--   Bousquet Theorem 2.1: sub-gamma cgf bound via Herbst double integration
-- statement:
--   **Bousquet sub-gamma cgf bound via Herbst double integration (Bousquet 2002 Theorem 2.1 integration step; BLM §12.4).**
--
--   In the entropy method, after Massart's modified log-Sobolev inequality (eq. (4)) and the per-summand bound (eq. (6)), the cumulant generating function $G(\lambda)=\log\mathbb{E}\,e^{\lambda(Z-\mathbb{E}Z)}$ of a *centered* random variable satisfies a second-order differential inequality of the form $G''(\lambda)\le v\,e^{\lambda}$, together with the centering data $G(0)=0$ and $G'(0)=0$ (the cgf and its slope vanish at the origin for a mean-zero variable). Here $v$ is the variance proxy $v=(1+u)\,\mathbb{E}Z+n\sigma^2$.
--
--   This lemma performs the two Herbst integrations. Integrating $G''\le v\,e^{\lambda}$ from $0$ with $G'(0)=0$ gives $G'(\lambda)\le v(e^{\lambda}-1)$; integrating again with $G(0)=0$ gives
--   $$G(L)\le v\,(e^{L}-1-L)=v\,\psi(-L),\qquad \psi(x)=e^{-x}-1+x.$$
--   This is exactly the sub-gamma cgf bound of Bousquet's Theorem 2.1, $\log\mathbb{E}\,e^{\lambda(Z-\mathbb{E}Z)}\le\psi(-\lambda)\,v$, and it is precisely the hypothesis consumed by the Bennett–Bernstein tail node `subgamma_chernoff_tail` (in MGF form $\operatorname{mgf}(Z-\mathbb{E}Z,\lambda)\le\exp((e^{\lambda}-1-\lambda)v)$).
--
--   The proof is two applications of the mean-value comparison principle `image_le_of_deriv_right_le_deriv_boundary` against the boundaries $B_1(x)=v(e^x-1)$ and $B_2(x)=v(e^x-1-x)$.
-- source:
--   Bousquet 2002, C.R.Acad.Sci.Paris Ser.I 334:495-500, Theorem 2.1 (integration of the differential inequality, eq. (4)-(6)); Klein-Rio 2005, Ann.Probab.33:1060-1077; Boucheron-Lugosi-Massart, Concentration Inequalities, OUP 2013, sec. 12.4 (Herbst argument).

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

theorem bousquet_cgf_le_phi_via_herbst
    (G G' G'' : ℝ → ℝ) (v L : ℝ) (hL : 0 ≤ L) (hv : 0 ≤ v)
    (hG0 : G 0 = 0) (hG'0 : G' 0 = 0)
    (hG_cont : ContinuousOn G (Set.Icc 0 L))
    (hG'_cont : ContinuousOn G' (Set.Icc 0 L))
    (hG_deriv : ∀ x ∈ Set.Ico (0:ℝ) L, HasDerivWithinAt G (G' x) (Set.Ici x) x)
    (hG'_deriv : ∀ x ∈ Set.Ico (0:ℝ) L, HasDerivWithinAt G' (G'' x) (Set.Ici x) x)
    (hG''_bound : ∀ x ∈ Set.Ico (0:ℝ) L, G'' x ≤ v * Real.exp x) :
    G L ≤ v * (Real.exp L - 1 - L) := by sorry
