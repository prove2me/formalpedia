-- Prove2me | Theorems.Thm_syracuse_initial_run_endpoint_and_growth
-- name    : syracuse_initial_run_endpoint_and_growth
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T11:40:17.59591+00:00
-- url     : https://prove2.me/theorems/cd5cee3d-2614-45b1-abbd-326d3f73988d
-- title:
--   The endpoint and strict growth of the initial Syracuse ascent
-- statement:
--   For $T(n)$ equal to the odd part of $3n+1$, write $n=2^k q-1$ where $k,q>0$. At every time $0<j<k$ the Syracuse orbit is above $n$. At time $k$ the value is exactly the odd part of $3^kq-1$. For the canonical factorization of $n+1$, the cofactor $q$ is odd.
-- source:
--   Initial-run identity for the Syracuse descent branch https://prove2.me/theorems/8c399870-0530-4747-94e9-5fb0717268d6.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_initial_run_endpoint_and_growth (k q : ℕ) (hk : 0 < k) (hq : 0 < q) :
    syracuseStep^[k] (2^k*q-1) = ordCompl[2] (3^k*q-1) ∧
    ∀ j : ℕ, 0 < j → j < k →
      2^k*q-1 < syracuseStep^[j] (2^k*q-1) := by sorry
