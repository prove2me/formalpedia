-- Prove2me | Theorems.Thm_divisor_reverse_orientation
-- name    : divisor_reverse_orientation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:18.329433+00:00
-- url     : https://prove2.me/theorems/8cec9a04-21e1-4014-9f99-903b034cf7e2
-- title:
--   divisor reverse orientation: divisor reverse orientation
-- statement:
--   The orientation divisors of $\mathcal{O}$ and its reverse sum to the canonical divisor:
--   $D(\mathcal{O}) + D(\overline{\mathcal{O}}) = K_G$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L945-L963
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L945-L963

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem divisor_reverse_orientation {G : CFGraph} (O : CFOrientation G)  : ordiv G O + ordiv G (O.reverse) = canonical_divisor G := by sorry
