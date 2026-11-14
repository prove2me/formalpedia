-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
-- name    : GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:48:20.337327+00:00
-- url     : https://prove2.me/theorems/0c669b1d-7cae-4052-be2a-3047a25d6dd7
-- title:
--   Reduced residue representatives and residue fibres
-- statement:
--   For a natural modulus $W$, the reduced residue representatives are the integers $b$ with $0\le b<W$ and $\gcd(W,b)=1$. In particular this set is empty when $W=0$.
--
--   For a finite set $S\subseteq\mathbb N$ and natural parameters $W,b$, the residue fibre is
--
--   $$
--   S_{W,b}=\{n\in S:n\bmod W=b\}.
--   $$
--
--   Applications use a positive modulus and its standard representatives. The formal definition is total: at modulus zero the natural-number remainder convention is $n\bmod0=n$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/ReducedResidues.lean#L10-L35

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Primorial
import Lean

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace Wikipedia.SzemeredisTheorem

open Finset

/-- The reduced residue system modulo `W`, represented by its standard
natural-number representatives in `[0, W)`. -/
def reducedResidues (W : ℕ) : Finset ℕ :=
  {b ∈ Finset.range W | W.Coprime b}







/-- The elements of `S` lying in the standard residue class `b` modulo
`W`. -/
def residueFiber (S : Finset ℕ) (W b : ℕ) : Finset ℕ :=
  {n ∈ S | n % W = b}

















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.reducedResidues.eq_1,
    `Wikipedia.SzemeredisTheorem.residueFiber.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


