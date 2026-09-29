-- Prove2me | Theorems.Thm_mme_CW_q6_z_hash_offset_label_card
-- name    : mme_CW_q6_z_hash_offset_label_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:00:52.373308+00:00
-- url     : https://prove2.me/theorems/ce98cf20-2ad7-4780-85b5-b30ff4b8992c
-- title:
--   Exact retained-offset multiplicity for one q=6 Z-hash
-- statement:
--   Fix a q=6 Z-word $z$ and a weight vector $w$ modulo $M$. Assume that $2$ is a unit modulo $M$, and let $S$ be a finite set of natural labels strictly below $M$. Then exactly $|S|$ affine offsets $b_0\in\mathbb Z/M\mathbb Z$ make the doubled Z-hash land on a doubled retained label:\n\n$$\n\bigl|\{b_0:\exists s\in S,\ h_Z(b_0,w,z)=2s\}\bigr|=|S|.\n$$\n\nThe statement supplies the exact label multiplicity for aggregating fixed-Z degree concentration over affine offsets. It only uses invertibility of $2$ and injectivity of the bounded natural labels modulo $M$; progression freeness is not needed at this stage.
-- source:
--   Affine-offset counting step in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 270--271

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open BigOperators MME

set_option autoImplicit false

theorem mme_CW_q6_z_hash_offset_label_card
    {M N : ℕ} [NeZero M]
    (h2 : IsUnit (2 : ZMod M))
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range M)
    (w : Fin (2 * N) → ZMod M)
    (z : Fin (2 * N) → Fin 3) :
    ((Finset.univ : Finset (ZMod M)).filter (fun b0 =>
      ∃ s ∈ S,
        cwQ6DoubledZHash b0 w z = 2 * (s : ZMod M))).card = S.card := by
  sorry
