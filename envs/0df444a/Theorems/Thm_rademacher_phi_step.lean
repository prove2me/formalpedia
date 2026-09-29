-- Prove2me | Theorems.Thm_rademacher_phi_step
-- name    : rademacher_phi_step
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/a24e919f-e868-5b33-8488-e7f48d65aa0f
-- title:
--   Rademacher's Φ under an ST^q-step
-- statement:
--   Let $c$ and $r$ be natural numbers with $c>0$ and $r>0$, and let $a,b,d,q$ be integers subject to the two relations $r=qc-d$ and $ad-bc=1$. Here, for an integer $h$ and a natural number $k$, the Dedekind sum is $\operatorname{dedekindSum}(h,k)=\sum_{n=0}^{k-1}\big(\!\big(n/k\big)\!\big)\,\big(\!\big(hn/k\big)\!\big)$, where the sawtooth $\big(\!\big(x\big)\!\big)$ is $0$ when the fractional part of $x$ vanishes and equals $\{x\}-\tfrac12$ otherwise. The assertion is the identity of rational numbers
--   $$\frac{a+d}{c}-12\,\operatorname{dedekindSum}(d,c)=\frac{(qa-b)+c}{r}-12\,\operatorname{dedekindSum}(c,r)+q-3,$$
--   the numerators $a+d$ and $qa-b+c$ being the images in $\mathbb{Q}$ of the corresponding integers and $c$ being read as an integer in the second Dedekind sum. In other words, writing $\Phi\begin{pmatrix}a&b\\c&d\end{pmatrix}=\frac{a+d}{c}-12\,s(d,c)$ for matrices with positive lower-left entry, one has $\Phi\begin{pmatrix}a&b\\c&d\end{pmatrix}=\Phi\begin{pmatrix}qa-b&a\\r&c\end{pmatrix}+q-3$. No inequality between $r$ and $c$ is assumed, only $r>0$.
--
--   This is the special case $B=ST^{q}$ of Rademacher's composition law $\Phi(AB)=\Phi(A)+\Phi(B)-3\operatorname{sign}(c_Ac_Bc_{AB})$ for the function $\Phi$ attached to Dedekind sums, in the shape needed for an induction on the lower-left entry $c$. It is used in the derivation of the transformation behaviour of the Dedekind $\eta$-function under $\mathrm{SL}_2(\mathbb{Z})$, by [`ModularForm.eta_specialLinearGroup_smul`](thm.html#ModularForm.eta_specialLinearGroup_smul) and [`ModularForm.logEta_specialLinearGroup_smul`](thm.html#ModularForm.logEta_specialLinearGroup_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_rademacher_phi_step.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem rademacher_phi_step (c r : ℕ) (hc : 0 < c) (hr : 0 < r) (a b d q : ℤ) (hrd : (r : ℤ) = q * c - d) (hdet : a * d - b * c = 1) : ((a + d : ℤ) : ℚ) / c - 12 * dedekindSum d c = ((q * a - b + c : ℤ) : ℚ) / r - 12 * dedekindSum c r + q - 3 := by sorry
