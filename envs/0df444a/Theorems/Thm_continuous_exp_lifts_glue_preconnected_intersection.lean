-- Prove2me | Theorems.Thm_continuous_exp_lifts_glue_preconnected_intersection
-- name    : continuous_exp_lifts_glue_preconnected_intersection
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:54.275585+00:00
-- url     : https://prove2.me/theorems/d8fc597d-a1de-4816-a6c4-6b9d8ff4ef13
-- title:
--   Gluing exponential lifts over a preconnected intersection
-- statement:
--   Let $S,T$ be closed subsets of a topological space $X$, with preconnected intersection (which may be empty). Let $f,g:X\to\mathbb C$ be continuous on $S$ and $T$, respectively, and suppose that $e^{f(x)}=e^{g(x)}$ for every $x\in S\cap T$. Then there is a function $k:X\to\mathbb C$, continuous on $S\cup T$, satisfying
--
--   $$e^{k(x)}=e^{f(x)}\quad(x\in S),\qquad e^{k(x)}=e^{g(x)}\quad(x\in T).$$
--
--   This is the logarithm-gluing step used in an analytic approach to planar separation.
-- source:
--   Adaptation of the lift-gluing step in Isabelle/HOL Jordan_Curve, proof of Janiszewski_weak, https://isabelle.in.tum.de/website-Isabelle2017/dist/library/HOL/HOL-Analysis/Jordan_Curve.html ; supporting work for https://prove2.me/theorems/499509f0-5564-4ad2-b052-bdaa0fac6f2b

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Piecewise

open Set

theorem continuous_exp_lifts_glue_preconnected_intersection {X : Type} [TopologicalSpace X]
    (S T : Set X) (f g : X → ℂ) (hS : IsClosed S) (hT : IsClosed T)
    (hW : IsPreconnected (S ∩ T)) (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) (S ∩ T)) :
    ∃ k : X → ℂ, ContinuousOn k (S ∪ T) ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (f x)) S ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (g x)) T := by sorry
