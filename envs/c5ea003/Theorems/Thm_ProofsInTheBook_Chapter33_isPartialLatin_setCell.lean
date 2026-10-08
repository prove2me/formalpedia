-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_isPartialLatin_setCell
-- name    : ProofsInTheBook.Chapter33.isPartialLatin_setCell
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:06:39.849632+00:00
-- url     : https://prove2.me/theorems/9f7a7d1a-9308-481d-b0c2-4998f2fb1165
-- title:
--   Filling an empty cell with an absent symbol
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. Let $n\in\mathbb N$, let $P$ be partial Latin, and let $i_0,j_0,a\in[n]$. Assume $P(i_0,j_0)=\bot$, that $a$ occurs nowhere in row $i_0$, and that $a$ occurs nowhere in column $j_0$. Then
--   $$Q(i,j)=\begin{cases}a&(i,j)=(i_0,j_0),\\P(i,j)&\text{otherwise}\end{cases}$$
--    is partial Latin.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33.lean#L663. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

lemma ProofsInTheBook.Chapter33.isPartialLatin_setCell {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    {i₀ j₀ a : Fin n} (hP : IsPartialLatin P) (_hempty : P i₀ j₀ = none)
    (haRow : a ∉ rowSymbols P i₀) (haCol : a ∉ colSymbols P j₀) :
    IsPartialLatin (setCell P i₀ j₀ a) := by sorry
