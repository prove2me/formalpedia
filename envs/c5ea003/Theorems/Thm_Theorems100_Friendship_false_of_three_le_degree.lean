-- Prove2me | Theorems.Thm_Theorems100_Friendship_false_of_three_le_degree
-- name    : Theorems100.Friendship.false_of_three_le_degree
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:41:50.292298+00:00
-- url     : https://prove2.me/theorems/d5e18bd1-11e4-491b-9763-83d12245dcb5
-- title:
--   A regular friendship graph cannot have degree at least three
-- statement:
--   Let G be a simple undirected graph on a finite nonempty vertex set V. Suppose every two distinct vertices have exactly one common neighbor, whether or not those two vertices are adjacent. Let $d\in\mathbb N$. The additional assumptions that every vertex has degree d and $d\ge3$ are inconsistent.
-- source:
--   Mathlib Archive original proof: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Archive/Wiedijk100Theorems/FriendshipGraphs.lean#L246. Archive authors: Aaron Anderson, Jalex Stark, and Kyle Miller; Apache 2.0 license retained. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 44, “Of friends and politicians”, pp. 307–309 (https://doi.org/10.1007/978-3-662-57265-8_44).

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

theorem Theorems100.Friendship.false_of_three_le_degree (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) : False := by sorry
