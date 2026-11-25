-- Prove2me | Theorems.Thm_collatz_smaller_visitors_at_second_iterate_exact
-- name    : collatz_smaller_visitors_at_second_iterate_exact
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:22:55.905336+00:00
-- url     : https://prove2.me/theorems/5da616e9-10eb-44ca-af6c-175d5d0eb823
-- title:
--   An exact affine-word criterion for smaller visitors to the second Collatz iterate
-- statement:
--   Let $C$ be the ordinary Collatz map with an odd step $xmapsto3x+1$ and an even step $xmapsto x/2$. For $nequiv15pmod{16}$, put $y=(3n+1)/2=C^2(n)$, which is odd.
--
--   For a finite list $w$ of positive halving counts let $L$ be its length, $E$ its sum, and let its affine offset be
--   $$
--   B([])=0,qquad B(a::v)=3^{|v|}+2^a B(v).
--   $$
--   The affine visitor condition is that some such list has
--   $$
--   z=2^E y-B(w)>0,qquad 3^Lmid z,qquad z<3^L n .
--   $$
--
--   Prove that the affine visitor condition is equivalent to the existence of a smaller positive start whose ordinary orbit reaches $C^2(n)$. Both the word length and the visitor clock are unrestricted.
-- source:
--   Sublemma of https://prove2.me/theorems/6f3e7bbf-31de-5661-9991-6e935b7e3c80. Uses the odd-step affine identity and an exact reconstruction of ordinary clocks.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_smaller_visitors_at_second_iterate_exact (n : ℕ) (hclass : n%16=15) :
    (∃ k t : ℕ, 0<k ∧ k<n ∧ collatzStep^[t] k=collatzStep^[2] n) ↔
    (∃ w : List ℕ, (∀ a∈w, 0<a) ∧
      let y := (3*n+1)/2
      let B := (w.foldr (fun a (p : ℕ × ℕ) => (p.1+1,3^p.1+2^a*p.2)) (0,0)).2
      let z := 2^w.sum*y-B
      0<z ∧ 3^w.length ∣ z ∧ z<3^w.length*n) := by
  sorry
