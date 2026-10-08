-- Prove2me | Theorems.Thm_Theorems100_Friendship_card_of_regular
-- name    : Theorems100.Friendship.card_of_regular
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:41:47.984481+00:00
-- url     : https://prove2.me/theorems/9a2af2bc-86ba-41bb-86be-869a55f516e9
-- title:
--   The number of vertices in a regular friendship graph
-- statement:
--   Let G be a simple undirected graph on a finite nonempty vertex set V. Suppose every two distinct vertices have exactly one common neighbor, whether or not those two vertices are adjacent. Let $d\in\mathbb N$ and assume every vertex has degree d. Then
--   $$d+(|V|-1)=d^2.$$
--   The subtraction is natural-number subtraction; nonemptiness ensures |V|>=1.
-- source:
--   Mathlib Archive original proof: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Archive/Wiedijk100Theorems/FriendshipGraphs.lean#L181. Archive authors: Aaron Anderson, Jalex Stark, and Kyle Miller; Apache 2.0 license retained. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 44, “Of friends and politicians”, pp. 307–309 (https://doi.org/10.1007/978-3-662-57265-8_44).

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

theorem Theorems100.Friendship.card_of_regular (hd : G.IsRegularOfDegree d) : d + (Fintype.card V - 1) = d * d := by sorry
