-- Prove2me | Theorems.Thm_config_degree_mono
-- name    : config_degree_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:38.094386+00:00
-- url     : https://prove2.me/theorems/118b1ceb-9aa7-4024-ba6c-edef2c800fc0
-- title:
--   config degree mono: config degree mono
-- statement:
--   The configuration degree is monotone: if $c \le c'$ pointwise, then
--   $\deg(c) \le \deg(c')$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L264-L267
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Config.lean#L264-L267

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem config_degree_mono {q : G.V} {c c' : Config G q} (h_le : c ≤ c') :
  config_degree c ≤ config_degree c' := by sorry
