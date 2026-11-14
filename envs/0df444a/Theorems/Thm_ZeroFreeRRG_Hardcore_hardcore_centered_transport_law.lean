-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_centered_transport_law
-- name    : ZeroFreeRRG.Hardcore.hardcore_centered_transport_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:21:03.732933+00:00
-- url     : https://prove2.me/theorems/ca7a9a6a-fc82-4347-a8de-6be4d3b9ba82
-- title:
--   Centered hardcore cavity law is invariant under transport
-- statement:
--   The hardcore affine cavity transport from occupation density $\alpha$ to $\alpha′$ preserves the centered-message probability law $h=(\mu_1-\alpha)/(1-\alpha)$.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_centered_transport_law (α α' : ℝ) (ha : 0 < α) (hlt : α < α') (ha' : α' < 1/2)
    (ν : ProbabilityMeasure (Fin 2 → ℝ)) (hν : ν ∈ cavityLaws .hardcore α)
    (ν' : ProbabilityMeasure (Fin 2 → ℝ))
    (hmap : (ν' : Measure (Fin 2 → ℝ)) = Measure.map
      (fun x : Fin 2 → ℝ => fun i =>
        (1-(1-α')/(1-α))*(if i.val=1 then 1 else 0) + ((1-α')/(1-α))*x i)
      (ν : Measure (Fin 2 → ℝ))) :
    Measure.map (fun x : Fin 2 → ℝ => (x 1-α')/(1-α')) (ν' : Measure (Fin 2 → ℝ)) =
      Measure.map (fun x : Fin 2 → ℝ => (x 1-α)/(1-α)) (ν : Measure (Fin 2 → ℝ)) := by sorry
