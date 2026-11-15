-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_reducedResidue_card_le_totient_mul_card_fiber
-- name    : Wikipedia.SzemeredisTheorem.exists_reducedResidue_card_le_totient_mul_card_fiber
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:02:34.996435+00:00
-- url     : https://prove2.me/theorems/fa752303-99ef-4b40-942b-6bd54e342f0d
-- title:
--   A reduced-residue pigeonhole bound without division
-- statement:
--   Let $W>0$ and let $S$ be a finite set of natural numbers, each coprime to $W$. There is a reduced residue $b$ modulo $W$ for which $|S|\le\varphi(W)|\operatorname{residueFiber}(S,W,b)|$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/ReducedResidues.lean#L58-L105

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Primorial

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Wikipedia.SzemeredisTheorem
open Finset

theorem Wikipedia.SzemeredisTheorem.exists_reducedResidue_card_le_totient_mul_card_fiber
    {W : ℕ} (hW : 0 < W) (S : Finset ℕ)
    (hcop : ∀ n ∈ S, n.Coprime W) :
    ∃ b ∈ reducedResidues W,
      #S ≤ W.totient * #(residueFiber S W b) := by sorry
