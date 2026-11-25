-- Prove2me | Theorems.Thm_collatz_residual_fifteen_mod_sixteen_after_all_second_run_exit_visitors
-- name    : collatz_residual_fifteen_mod_sixteen_after_all_second_run_exit_visitors
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-25T20:57:49.722866+00:00
-- url     : https://prove2.me/theorems/465faa10-2164-5cf8-95ed-b77fc9a7c2dd
-- title:
--   Remaining 15-mod-16 mergers after all visits through the second odd-run exit
-- statement:
--   Retain every hypothesis of the [parent residual](https://prove2.me/theorems/5b7d9a89-44c1-4773-99fa-a4c0ee992df8).
--
--   Let $C$ be the ordinary Collatz map. For $x>0$, put
--   $$
--   r(x)=v_2(x+1),\qquad W(x)=3^{r(x)}(x+1)/2^{r(x)}-1,
--   $$
--   and let $s(x)=v_2(W(x))$, $J(x)=W(x)/2^{s(x)}$, and $D(x)=2r(x)+s(x)$. Thus $J(x)$ is the odd run exit that follows the initial $r(x)$ odd-step pairs and the remaining $s(x)$ halvings. For a start $n>0$, let $T=D(n)+D(J(n))$ and $y=J(J(n))$.
--
--   A finite list $v$ of positive halving counts has length $L$ and total $E$. Set $B([])=0$ and $B(a::u)=3^{|u|}+2^aB(u)$. Say the affine condition holds if some such list satisfies
--   $$
--   z=2^E y-B(v)>0,\qquad 3^L\mid z,\qquad z<3^L n .
--   $$
--
--   Assume that the affine condition fails. Prove that a positive start smaller than $n$ shares an ordinary Collatz iterate with $n$.
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n,\qquad C^a(n)=C^b(k).
--   $$
-- source:
--   Auxiliary to https://prove2.me/theorems/5b7d9a89-44c1-4773-99fa-a4c0ee992df8. Extends the exact odd-target affine criterion through both initial run exits.

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_residual_fifteen_mod_sixteen_after_all_second_run_exit_visitors (n : ℕ)
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
      3^(r+3) ∣ 2^(a+b)*4^s*(3*n+1)+18-(2^(a+b)+3*2^b)))
    (hfirstRunVisitor : ¬ (let r := (n+1).factorization 2
    let w := 3^r*((n+1)/2^r)-1
    let s := w.factorization 2
    ∃ v : List ℕ, (∀ a∈v, 0<a) ∧
      let B := (v.foldr (fun a (p : ℕ × ℕ) => (p.1+1,3^p.1+2^a*p.2)) (0,0)).2
      let z := 2^v.sum*(w/2^s)-B
      0<z ∧ 3^v.length ∣ z ∧ z<3^v.length*n))
    (hLateResidue : ¬ (∃ p : ℕ × ℕ, p∈([(1224440064, 524071407), (11019960576, 2338056687), (11019960576, 2957834991),
      (11019960576, 3862823151), (11019960576, 6016620015), (11019960576, 6497574639),
      (11019960576, 6918369519), (11019960576, 7647666159), (11019960576, 8278858479),
      (11019960576, 8544237807), (11019960576, 8578203375), (11019960576, 9083530735),
      (11019960576, 10717660911), (11019960576, 10768609263), (22039921152, 15112762095),
      (99179645184, 57926895), (99179645184, 236993263), (99179645184, 818377455),
      (99179645184, 2643882991), (99179645184, 3611896815), (99179645184, 4273203183),
      (99179645184, 4278013167), (99179645184, 5557880559), (99179645184, 5635018479),
      (99179645184, 5765693679)] : List (ℕ × ℕ)) ∧ n%p.1=p.2))
    (hsecondRunVisitor : ¬ (let runEnd : ℕ → ℕ := fun x =>
      let r := (x+1).factorization 2
      3^r*((x+1)/2^r)-1
    let jump : ℕ → ℕ := fun x =>
      let w := runEnd x
      w/2^(w.factorization 2)
    ∃ v : List ℕ, (∀ a∈v, 0<a) ∧
      let y := jump (jump n)
      let B := (v.foldr (fun a (p : ℕ × ℕ) => (p.1+1,3^p.1+2^a*p.2)) (0,0)).2
      let z := 2^v.sum*y-B
      0<z ∧ 3^v.length ∣ z ∧ z<3^v.length*n)) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  sorry
