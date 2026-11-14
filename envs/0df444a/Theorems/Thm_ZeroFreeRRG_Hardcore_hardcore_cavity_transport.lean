-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_cavity_transport
-- name    : ZeroFreeRRG.Hardcore.hardcore_cavity_transport
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:03:44.710307+00:00
-- url     : https://prove2.me/theorems/ec64dfa5-6790-452c-8cc7-606d2a207219
-- title:
--   Hardcore cavity-law transport with parameter slack
-- statement:
--   Fix $0<\alpha<\alpha′<1/2$ and let $\nu$ be a hardcore cavity law at $\alpha$. Set $c=(1-\alpha′)/(1-\alpha)$. Then $0<c<1$, and sending a message $x$ to $c x+(1-c)(0,1)$ transports $\nu$ to a cavity law at $\alpha′$. A nontrivial law remains nontrivial. This is the law transport used in the hardcore comparison in the proof of Lemma 4.17.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical BigOperators
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem hardcore_cavity_transport (a a' : ℝ) (ha : 0 < a) (hlt : a < a') (ha' : a' < 1/2)
    (ν : ProbabilityMeasure ((.hardcore : Model).Spin → ℝ)) (hν : ν ∈ cavityLaws .hardcore a) :
    let c := (1-a')/(1-a)
    0 < c ∧ c < 1 ∧ ∃ ν' ∈ cavityLaws .hardcore a',
      (ν ≠ diracPi .hardcore a → ν' ≠ diracPi .hardcore a') ∧
      (ν' : Measure ((.hardcore : Model).Spin → ℝ)) =
        Measure.map (fun x : ((.hardcore : Model).Spin → ℝ) => fun i =>
          (1-c)*(if i.val = 1 then 1 else 0) + c*x i) (ν : Measure _) := by sorry
end ZeroFreeRRG.Hardcore
