-- Prove2me | Theorems.Thm_ZInQ_Literature_grossZagier
-- name    : ZInQ.Literature.grossZagier
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T20:07:30.277837+00:00
-- url     : https://prove2.me/theorems/65bcff95-fa24-45d9-a255-667d27254892
-- title:
--   Gross–Zagier (positive-rank half)
-- statement:
--   The positive-rank half of the Gross–Zagier theorem, for every elliptic curve over $\mathbb{Q}$. If $E/\mathbb{Q}$ is an elliptic curve and $F$ is an entire continuation of its $L$-series $L(E,s)$ (agreeing with it on $\Re s>3/2$) whose order of vanishing at $s=1$ is exactly $1$, then $E(\mathbb{Q})$ contains a point of infinite order. This is the analytic-rank-one implies positive-algebraic-rank direction. Literature: Gross–Zagier (Invent. Math. 84, 1986) with an auxiliary imaginary quadratic twist (Bump–Friedberg–Hoffstein) and modularity (Breuil–Conrad–Diamond–Taylor).
-- source:
--   https://github.com/elliotglazer/diophantine-z-q/blob/964d7dd71f253091dbc5eac793b78cc56d1fcc73/ZInQKernel/Hypotheses/CR3Literature.lean#L62-L70

import Mathlib
import Definitions.Def_ZInQLiterature

theorem ZInQ.Literature.grossZagier : ZInQ.Literature.GrossZagier := by sorry
