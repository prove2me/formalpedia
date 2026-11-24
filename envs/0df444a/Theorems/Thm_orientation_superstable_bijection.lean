-- Prove2me | Theorems.Thm_orientation_superstable_bijection
-- name    : orientation_superstable_bijection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:51:23.910119+00:00
-- url     : https://prove2.me/theorems/8754552b-a54e-4785-88a4-91e22e19d67a
-- title:
--   orientation superstable bijection: orientation superstable bijection
-- statement:
--   The bijection between acyclic orientations with unique source $q$ and maximal
--   superstable configurations.
--
--   See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 4.8,
--   part 3 (bijection).
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L1199-L1259
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Orientation.lean#L1199-L1259

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset

theorem orientation_superstable_bijection (G : CFGraph) (q : G.V) :
    let α := {O : CFOrientation G // acyclic_with_unique_source G O q};
    let β := {c : Config G q // maximal_superstable G c};
    let f_raw : α → Config G q := λ O_sub => orientation_to_config G O_sub.val q O_sub.prop;
    let f : α → β := λ O_sub => ⟨f_raw O_sub, orientation_config_maximal G O_sub.val q O_sub.prop⟩;
    Function.Bijective f := by sorry
