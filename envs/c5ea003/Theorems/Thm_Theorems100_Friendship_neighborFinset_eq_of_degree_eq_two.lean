-- Prove2me | Theorems.Thm_Theorems100_Friendship_neighborFinset_eq_of_degree_eq_two
-- name    : Theorems100.Friendship.neighborFinset_eq_of_degree_eq_two
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:42:13.710526+00:00
-- url     : https://prove2.me/theorems/6056feb3-2cac-41fb-b9b4-b3c404511959
-- title:
--   Neighbors in a degree-two friendship graph
-- statement:
--   Let G be a simple undirected graph on a finite nonempty vertex set V. Suppose every two distinct vertices have exactly one common neighbor, whether or not those two vertices are adjacent. Assume every vertex has degree 2. For every $v\in V$,
--   $$N_G(v)=V\setminus\{v\}.$$
--   Here $N_G(v)$ is the finite set of vertices adjacent to v.
-- source:
--   Mathlib Archive original proof: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Archive/Wiedijk100Theorems/FriendshipGraphs.lean#L287. Archive authors: Aaron Anderson, Jalex Stark, and Kyle Miller; Apache 2.0 license retained. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 44, “Of friends and politicians”, pp. 307–309 (https://doi.org/10.1007/978-3-662-57265-8_44).

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

theorem Theorems100.Friendship.neighborFinset_eq_of_degree_eq_two (hd : G.IsRegularOfDegree 2) (v : V) :
    G.neighborFinset v = Finset.univ.erase v := by sorry
