-- Prove2me | Definitions.Def_BookSixthRandomGraph
-- name    : BookSixthRandomGraph
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-09-16T16:28:30.70829+00:00
-- url     : https://prove2.me/theorems/e6e940ee-65c0-4788-a372-4720dbbc6160
-- title:
--   Random graph model for girth
-- statement:
--   Random graph model $G(n,p)$ for the probabilistic-method girth argument. Edge slots are unordered distinct vertex pairs; `slotOf` orders a pair; `cycSucc` is wraparound successor for cycle indexing; `graphWeight` is the independent per-slot Bernoulli product; `cycleEdges` collects the consecutive-pair slots of an injective vertex map over boundary data it receives. All data is explicit and finite.
-- source:
--   Random graph model for the high-girth high-chromatic-number argument, Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 3 setting, https://doi.org/10.1007/978-3-662-57265-8_45

import Mathlib

set_option autoImplicit false

namespace BookSixth

/-- Unordered distinct-vertex pairs as edge slots for random graphs. -/
abbrev edgeSlots (n : Nat) := {p : Prod (Fin n) (Fin n) // p.1 < p.2}

/-- Order two distinct vertices into a slot. -/
def slotOf {n : Nat} (u v : Fin n) (h : Ne u v) : edgeSlots n :=
  if hlt : u < v then Subtype.mk (u, v) hlt
  else Subtype.mk (v, u) ((lt_or_gt_of_ne h).resolve_left hlt)

/-- Cyclic successor on Fin l (wraps around), for cycle indexing. -/
def cycSucc {l : Nat} (hl : 0 < l) (i : Fin l) : Fin l :=
  Fin.mk ((i.val + 1) % l) (by apply Nat.mod_lt; exact hl)

/-- G(n,p) weight: independent per-slot Bernoulli product. -/
noncomputable def graphWeight (n : Nat) (p : Real) (b : edgeSlots n -> Bool) : Real :=
  Finset.prod Finset.univ (fun s => if b s then p else 1 - p)

/-- Cycle edges of a vertex map: consecutive pairs ordered into slots. -/
noncomputable def cycleEdges {n l : Nat} (v : Fin l -> Fin n)
    (hinj : Function.Injective v) (hl3 : Nat.le 3 l)
    (hne : forall i : Fin l, Ne (cycSucc (lt_of_lt_of_le (by norm_num) hl3) i) i) :
    Finset (edgeSlots n) :=
  have hpos : 0 < l := lt_of_lt_of_le (by norm_num) hl3
  Finset.image (fun i : Fin l => slotOf (v i) (v (cycSucc hpos i))
    (fun hcon => absurd (hinj hcon) (Ne.symm (hne i)))) Finset.univ

end BookSixth


