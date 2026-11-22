-- Prove2me | Theorems.Thm_ZInQ_frozenTarget
-- name    : ZInQ.frozenTarget
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T20:10:51.172674+00:00
-- url     : https://prove2.me/theorems/830c63c0-af24-47f9-9e00-ce761ff8ce96
-- title:
--   Theorem 1.1 — $\mathbb{Z}$ is Diophantine in $\mathbb{Q}$ (bounded polynomial)
-- statement:
--   The goal of the mission (Theorem 1.1 of the manuscript). There exists a polynomial $P\in\mathbb{Z}[X_0,\dots,X_{n-1}]$ with $n=292\,890\,231\,905$ variables such that
--   $$\deg P<2\uparrow\uparrow 7,\qquad |c_m(P)|<2\uparrow\uparrow 8\ \text{for every coefficient},$$
--   and for every rational $q$,
--   $$\bigl(\exists\,\mathbf{w}\in\mathbb{Q}^{n-1},\ P(q,\mathbf{w})=0\bigr)\iff q\in\mathbb{Z}.$$
--   Here $\uparrow\uparrow$ denotes tetration. This exhibiting polynomial gives a Diophantine definition of the integers inside the rationals, which would imply the undecidability of Hilbert's tenth problem over $\mathbb{Q}$. The repository's kernel already proves this statement conditionally on the arithmetic inputs $H$ and CR$_3$; the mission formalizes those inputs to obtain the unconditional theorem.
-- source:
--   https://github.com/elliotglazer/diophantine-z-q/blob/964d7dd71f253091dbc5eac793b78cc56d1fcc73/ZInQKernel/Target.lean#L13-L26 ; https://github.com/elliotglazer/diophantine-z-q/blob/964d7dd71f253091dbc5eac793b78cc56d1fcc73/ZInQKernel/Main.lean

import Mathlib
import Definitions.Def_ZInQTarget

theorem ZInQ.frozenTarget : ZInQ.FrozenTarget := by sorry
