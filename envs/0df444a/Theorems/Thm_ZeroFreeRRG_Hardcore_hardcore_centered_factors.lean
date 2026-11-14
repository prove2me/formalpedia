-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_centered_factors
-- name    : ZeroFreeRRG.Hardcore.hardcore_centered_factors
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:00:36.871738+00:00
-- url     : https://prove2.me/theorems/74159520-726d-413e-9582-164890ca58cc
-- title:
--   Centered hardcore cavity and edge factors
-- statement:
--   Let $0<\alpha<1/2$ and let $x,y$ be two real vectors whose coordinates sum to one. Write $\theta=\alpha/(1-\alpha)$, $h=(x_1-\alpha)/(1-\alpha)$ and $k=(y_1-\alpha)/(1-\alpha)$. Then the two entries of the hardcore cavity interaction $M_\alpha x$ are $1+\theta h$ and $1-h$, and the edge factor is $1-hk$. These are the pointwise identities in equation (25).
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 29, equation (25).

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical BigOperators

namespace ZeroFreeRRG.Hardcore
theorem hardcore_centered_factors (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    (x y : Fin 2 → ℝ) (hx : (∑ i, x i) = 1) (hy : (∑ i, y i) = 1) :
    let θ := a/(1-a)
    let h := (x 1-a)/(1-a)
    let k := (y 1-a)/(1-a)
    Mmul .hardcore a x (0 : Fin 2) = 1+θ*h ∧
    Mmul .hardcore a x (1 : Fin 2) = 1-h ∧
    edgeFactor .hardcore a x y = 1-h*k := by sorry
end ZeroFreeRRG.Hardcore
