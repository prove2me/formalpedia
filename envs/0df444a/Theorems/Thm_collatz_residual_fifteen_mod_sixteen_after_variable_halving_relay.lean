-- Prove2me | Theorems.Thm_collatz_residual_fifteen_mod_sixteen_after_variable_halving_relay
-- name    : collatz_residual_fifteen_mod_sixteen_after_variable_halving_relay
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-25T20:12:14.317959+00:00
-- url     : https://prove2.me/theorems/6f3e7bbf-31de-5661-9991-6e935b7e3c80
-- title:
--   Remaining 15-mod-16 mergers after the variable-halving relay
-- statement:
--   Retain every hypothesis of the [parent residual](https://prove2.me/theorems/a1df4edc-8b63-51f9-989f-fd985c8c12bc).
--
--   Let $C$ be the ordinary Collatz map. For a start $n$, consider a nonnegative integer $s$, a positive integer $r$, and halving counts $a,bge2$. Put
--   $$
--   P=2^{a+b}4^s,qquad D=2^{a+b}+3cdot2^b .
--   $$
--   The two arithmetic conditions are
--   $$
--   2^r Ple3^{r+2},qquad
--   3^{r+3}mid P(3n+1)+18-D .
--   $$
--
--
--   Assume that no choice of the four parameters satisfies both arithmetic conditions. Prove that a smaller positive start shares an ordinary Collatz iterate with $n$.
--
--   The desired conclusion is
--   $$
--   \exists k,i,j\in\mathbb N,\qquad 0<k<n,\qquad C^i(n)=C^j(k).
--   $$
-- source:
--   Sublemma of https://prove2.me/theorems/a1df4edc-8b63-51f9-989f-fd985c8c12bc. Extends the preceding variable dyadic relay by allowing the two intervening halving counts to vary independently.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_residual_fifteen_mod_sixteen_after_variable_halving_relay (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575)
    (h2187 : n % 2187 ∉ [205, 325, 919, 991, 1000, 1090, 1171, 2170])
    (h19683 : n % 19683 ∉ ([154, 433, 1384, 1663, 2134, 2548, 3268, 3364,
      3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517,
      6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187,
      12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376] : List ℕ))
    (hfirst : let L := (n+1).factorization 2
      let q := (n+1)/2^L
      let P := 3^L*q
      ¬ (P % 4 = 1 ∨
      P % 256 ∈ ([43] : List ℕ) ∨
      P % 512 ∈ ([199, 363] : List ℕ) ∨
      P % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
      P % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
      P % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
      P % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ) ∨
      (P % 4 = 3 ∧ ∃ s : ℕ, 2 ≤ s ∧ 2^s ∣ 3*P-1 ∧ 3*3^L+2^s ≤ 2^(L+s))))
    (hsecond : let L := (n+1).factorization 2
      let q := (n+1)/2^L
      let X := (3^L*q-1)/2
      let H := (X+1).factorization 2
      let Q := (X+1)/2^H
      let W := 3^H*Q
      ¬ ((L ≤ 4 ∧ 3 ≤ H ∧
        (W % 256 ∈ ([43] : List ℕ) ∨
        W % 512 ∈ ([199, 363] : List ℕ) ∨
        W % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
        W % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
        W % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
        W % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ))) ∨
      (L ≤ 7 ∧ 5 ≤ H ∧
        (W % 16384 ∈ ([303, 2731, 6371] : List ℕ) ∨
        W % 32768 ∈ ([12715, 18659, 20783, 23211] : List ℕ) ∨
        W % 65536 ∈ ([1131, 8419, 15019, 25259, 26851, 30339, 37291, 39215, 45359, 47275, 60263] : List ℕ))) ∨
      (L ≤ 12 ∧ 7 ≤ H ∧
        (W % 262144 ∈ ([4551, 43691, 198427, 208743] : List ℕ))) ∨
      (∃ s : ℕ, 2^s ∣ W-1 ∧ W ≤ 2^s*(n))))
    (hexit : let L := (n+1).factorization 2
      let q := (n+1)/2^L
      let X := (3^L*q-1)/2
      let H := (X+1).factorization 2
      let Q := (X+1)/2^H
      let W := 3^H*Q
      ¬ (∃ s r : ℕ, 1 ≤ s ∧ r ≤ H ∧ 2^s ∣ W-1 ∧
        2^(s-1)%3^r=1 ∧ 2^r*(W+2^(s-1)-1) ≤ 3^r*2^(s-1)*n))
    (hmacro : ¬ (let runEnd : ℕ → ℕ := fun x =>
        let r := (x+1).factorization 2
        3^r*((x+1)/2^r)-1
      let jump : ℕ → ℕ := fun x =>
        let w := runEnd x
        w/2^(w.factorization 2)
      ∃ j s e : ℕ,
        let w := runEnd (jump^[j] n)
        let y := w/2^s
        let z := 2^e*y+1
        let r := z.factorization 3
        2^s ∣ w ∧ (y < n ∨ 2^r*(z/3^r)-1 < n)))
    (hordinary : ¬ (∃ t e : ℕ,
      let y := collatzStep^[t] n
      let z := 2^e*y+1
      let r := z.factorization 3
      2^r*(z/3^r)-1<n))
    (htwo : ¬ (∃ t e h d : ℕ,
      let y := collatzStep^[t] n
      let z := 2^e*y+1
      let x := 2^h*(z/3^h)-1
      let w := 2^d*x+1
      let r := w.factorization 3
      3^h ∣ z ∧ 2^r*(w/3^r)-1<n))
    (hsix : ¬ (∃ a : ℕ × ℕ, a ∈
      ([(69984, 14335),
       (629856, 146527),
       (5668704, 3995647),
       (51018336, 37378015),
       (153055008, 109181599),
       (1377495072, 840444415),
       (12397455648, 3901544575),
       (37192366944, 6197369695),
       (334731302496, 208689145279),
       (3012581722464, 2737770097471),
       (27113235502176, 1064113584991),
       (81339706506528, 74370268831615),
       (732057358558752, 472031056196863),
       (6588516227028768, 2749542838379647),
       (19765548681086304, 6653848750692991),
       (177889938129776736, 169170582350735935),
       (1601009443167990624, 307529423118340063)] : List (ℕ × ℕ)) ∧ n%a.1=a.2))
    (hsearch : ¬ ((n%9=7 ∧
      let next : ℕ → ℕ := fun v =>
        if 0<v ∧ v<6*n+2 then
          if v<n then v
          else if v%3=2 then (2*v-1)/3
          else if v%3=1 ∧ 2*v<6*n+2 then (4*v-1)/3
          else 0
        else 0
      let u := next^[6*n+1] ((32*n+1)/9)
      0<u ∧ u<n) ∨ n%2187=444 ∨ n%6561=4408 ∨ n%19683=3229))
    (hrelay : ¬ (∃ s r : ℕ, 0<s ∧ 0<r ∧ 2^r*(16*4^s)≤3^(r+2) ∧
      3^(r+3) ∣ 16*4^s*(3*n+1)-10))
    (hvariable : ¬ (∃ s r a b : ℕ, 0<r ∧ 2≤a ∧ 2≤b ∧
      2^r*(2^(a+b)*4^s)≤3^(r+2) ∧
      3^(r+3) ∣ 2^(a+b)*4^s*(3*n+1)+18-(2^(a+b)+3*2^b))) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
