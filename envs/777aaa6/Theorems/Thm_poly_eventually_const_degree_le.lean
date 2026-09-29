-- Prove2me | Theorems.Thm_poly_eventually_const_degree_le
-- name    : poly_eventually_const_degree_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-22T14:08:07.358513+00:00
-- url     : https://prove2.me/theorems/c7442e91-dcc7-4f59-8dca-69e52b186549
-- statement:
--   If a complex polynomial's evaluation is constant on a neighborhood of a point $c$ (i.e. $f(z)=f(c)$ for all $z$ near $c$), then $f$ has degree at most $0$ — by the identity theorem, $f$ is the constant polynomial $f(c)$.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
open Polynomial Filter Topology

theorem poly_eventually_const_degree_le {f : ℂ[X]} {c : ℂ} (h : ∀ᶠ z in 𝓝 c, f.eval z = f.eval c) : degree f ≤ 0 := by sorry
