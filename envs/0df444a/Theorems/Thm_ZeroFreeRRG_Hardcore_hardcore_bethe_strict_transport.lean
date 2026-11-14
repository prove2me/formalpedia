-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_bethe_strict_transport
-- name    : ZeroFreeRRG.Hardcore.hardcore_bethe_strict_transport
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:22:13.900146+00:00
-- url     : https://prove2.me/theorems/35b0725d-5c1d-4f2f-b917-140c8dcf6e69
-- title:
--   Strict Bethe improvement under hardcore cavity transport
-- statement:
--   For $0<\alpha<\alpha′<1/2$ and $d\ge2$, take a nontrivial hardcore cavity law at $\alpha$ and transport it affinely to a cavity law at $\alpha′$ as displayed in the formal statement. Its Bethe functional strictly increases under this transport.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_bethe_strict_transport (d : ℕ) (hd : 2 ≤ d) (α α' : ℝ) (ha : 0 < α) (hlt : α < α') (ha' : α' < 1/2)
    (ν : ProbabilityMeasure (Fin 2 → ℝ)) (hν : ν ∈ cavityLaws .hardcore α)
    (hne : ν ≠ diracPi .hardcore α)
    (ν' : ProbabilityMeasure (Fin 2 → ℝ)) (hν' : ν' ∈ cavityLaws .hardcore α')
    (hmap : (ν' : Measure (Fin 2 → ℝ)) = Measure.map
      (fun x : Fin 2 → ℝ => fun i =>
        (1-(1-α')/(1-α))*(if i.val=1 then 1 else 0) + ((1-α')/(1-α))*x i)
      (ν : Measure (Fin 2 → ℝ))) :
    betheK .hardcore α d ν < betheK .hardcore α' d ν' := by sorry
