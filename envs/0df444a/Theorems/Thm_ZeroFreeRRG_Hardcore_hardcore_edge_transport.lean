-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_edge_transport
-- name    : ZeroFreeRRG.Hardcore.hardcore_edge_transport
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:07:24.747866+00:00
-- url     : https://prove2.me/theorems/ad822e59-bf72-48ae-b366-494b68d1aa14
-- title:
--   Hardcore centered coordinates and edge factor are preserved by transport
-- statement:
--   Fix $0<\alpha<\alpha′<1/2$ and let $x,y$ be two real vectors whose coordinates sum to one. Let $c=(1-\alpha′)/(1-\alpha)$ and $Tz=c z+(1-c)(0,1)$. The transported vectors also sum to one, the centered coordinates $(z_1-\alpha)/(1-\alpha)$ are preserved, and the hardcore edge factor satisfies $E_{\alpha′}(Tx,Ty)=E_{\alpha}(x,y)$. This is the pointwise edge-factor invariance used in the hardcore Bethe comparison.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed pp. 29–30, equation (25).

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical BigOperators

namespace ZeroFreeRRG.Hardcore
theorem hardcore_edge_transport (a a' : ℝ) (ha : 0 < a) (hlt : a < a') (ha' : a' < 1/2)
    (x y : Fin 2 → ℝ) (hx : (∑ i, x i) = 1) (hy : (∑ i, y i) = 1) :
    let c := (1-a')/(1-a)
    let T := fun (x : Fin 2 → ℝ) i => (1-c)*(if i.val = 1 then 1 else 0) + c*x i
    (∑ i, T x i) = 1 ∧ (∑ i, T y i) = 1 ∧
    (T x 1-a')/(1-a') = (x 1-a)/(1-a) ∧
    (T y 1-a')/(1-a') = (y 1-a)/(1-a) ∧
    edgeFactor .hardcore a' (T x) (T y) = edgeFactor .hardcore a x y := by sorry
end ZeroFreeRRG.Hardcore
