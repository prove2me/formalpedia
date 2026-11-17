-- Prove2me | Theorems.Thm_ZMod_division_carry_assoc
-- name    : ZMod.division_carry_assoc
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:39.42076+00:00
-- url     : https://prove2.me/theorems/09443c2f-3f2f-47fd-9d0b-3106060b435b
-- title:
--   Associativity of carries for addition modulo $71$
-- statement:
--   Let $a,b,c∈ℤ/71ℤ$, and write $[a],[b],[c]∈\{0,…,70\}$ for their standard representatives. Define the carry by $κ(a,b)=⌊([a]+[b])/71⌋$. Then $$κ(a,b)+κ(a+b,c)=κ(b,c)+κ(a,b+c).$$ This identity supplies associativity for the carry-corrected group law on division fibres.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false

theorem ZMod.division_carry_assoc (a b c : ZMod 71) :
    (a.val + b.val) / 71 + ((a + b).val + c.val) / 71 =
      (b.val + c.val) / 71 + (a.val + (b + c).val) / 71 := by sorry
