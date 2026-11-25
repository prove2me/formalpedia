-- Prove2me | Theorems.Thm_collatz_residual_fifteen_mod_sixteen_after_sixfold_progression_classes
-- name    : collatz_residual_fifteen_mod_sixteen_after_sixfold_progression_classes
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-25T19:46:40.723706+00:00
-- url     : https://prove2.me/theorems/b7ac112c-5a9d-5208-a0ec-fa2cf7531dbc
-- title:
--   Remaining 15-mod-16 mergers after the sixfold congruence certificates
-- statement:
--   Retain all hypotheses of the [residual after two-run visitors](https://prove2.me/theorems/db9b60ec-72e1-5e71-adc2-467b3036fcef). Suppose also that the start belongs to none of the following congruence classes.
--
--   - $n\equiv 14335\pmod{69984}$
--   - $n\equiv 146527\pmod{629856}$
--   - $n\equiv 3995647\pmod{5668704}$
--   - $n\equiv 37378015\pmod{51018336}$
--   - $n\equiv 109181599\pmod{153055008}$
--   - $n\equiv 840444415\pmod{1377495072}$
--   - $n\equiv 3901544575\pmod{12397455648}$
--   - $n\equiv 6197369695\pmod{37192366944}$
--   - $n\equiv 208689145279\pmod{334731302496}$
--   - $n\equiv 2737770097471\pmod{3012581722464}$
--   - $n\equiv 1064113584991\pmod{27113235502176}$
--   - $n\equiv 74370268831615\pmod{81339706506528}$
--   - $n\equiv 472031056196863\pmod{732057358558752}$
--   - $n\equiv 2749542838379647\pmod{6588516227028768}$
--   - $n\equiv 6653848750692991\pmod{19765548681086304}$
--   - $n\equiv 169170582350735935\pmod{177889938129776736}$
--   - $n\equiv 307529423118340063\pmod{1601009443167990624}$
--
--   Prove that the ordinary orbit of $n$ meets the ordinary orbit of a smaller positive start.
--
--   The desired merger is
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n,\qquad C^a(n)=C^b(k).
--   $$
-- source:
--   Sublemma of https://prove2.me/theorems/db9b60ec-72e1-5e71-adc2-467b3036fcef. The inverse relay and choice of rounds follow Sections 4 and 5 of https://rstation.ai/problems/collatz/papers/213.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_residual_fifteen_mod_sixteen_after_sixfold_progression_classes (n : ℕ)
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
       (1601009443167990624, 307529423118340063)] : List (ℕ × ℕ)) ∧ n%a.1=a.2)) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
