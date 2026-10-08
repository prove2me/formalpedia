-- Prove2me | Theorems.Thm_Theorems100_Friendship_isRegularOf_not_existsPolitician
-- name    : Theorems100.Friendship.isRegularOf_not_existsPolitician
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:42:00.97465+00:00
-- url     : https://prove2.me/theorems/d478936d-8a28-4b23-9db1-667f542ee008
-- title:
--   A friendship graph without a universal neighbor is regular
-- statement:
--   Let G be a simple undirected graph on a finite nonempty vertex set V. Suppose every two distinct vertices have exactly one common neighbor, whether or not those two vertices are adjacent. Assume there is no vertex adjacent to every other vertex. Then there exists $d\in\mathbb N$ such that every vertex has degree d.
-- source:
--   Mathlib Archive original proof: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Archive/Wiedijk100Theorems/FriendshipGraphs.lean#L146. Archive authors: Aaron Anderson, Jalex Stark, and Kyle Miller; Apache 2.0 license retained. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 44, “Of friends and politicians”, pp. 307–309 (https://doi.org/10.1007/978-3-662-57265-8_44).

import Init
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib
import Definitions.Def_P2MAssembly_Chapter40
open Theorems100
open Finset SimpleGraph Matrix
universe u v
variable {V : Type u} {R : Type v} [Semiring R]
variable [Fintype V] {G : SimpleGraph V} {d : ℕ} (hG : Friendship G)
open Theorems100.Friendship
variable (R)
variable {R}
variable [Nonempty V]
open scoped Classical
include hG

theorem Theorems100.Friendship.isRegularOf_not_existsPolitician (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by sorry
