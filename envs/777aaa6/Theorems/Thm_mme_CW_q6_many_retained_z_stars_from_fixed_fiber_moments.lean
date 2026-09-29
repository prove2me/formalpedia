-- Prove2me | Theorems.Thm_mme_CW_q6_many_retained_z_stars_from_fixed_fiber_moments
-- name    : mme_CW_q6_many_retained_z_stars_from_fixed_fiber_moments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:17:55.996752+00:00
-- url     : https://prove2.me/theorems/72ca008b-535b-46e7-a4aa-bfdedd095e54
-- title:
--   Fixed-fiber moments aggregate to many retained q=6 Z-stars
-- statement:
--   Let $Z$ be a finite family of q=6 Z-words. Above every $z\in Z$, suppose there are exactly $B>0$ exact coupled addresses, and let $D_z(w)$ count those satisfying the doubled X-minus-Z equation at weight $w$. Assume $M>2$, $2$ is a unit modulo $M$, the middle profile is positive, and $2MH\le B$. For any finite label set $S\subseteq\{0,\ldots,M-1\}$, there are common affine parameters $(w,b_0)$ such that\n\n$$\nB|S||Z|\le 4M(2M+B)\,\bigl|\{z\in Z:H\le D_z(w),\ h_Z(b_0,w,z)\in2S\}\bigr|.\n$$\n\nThus fixed-Z concentration and exact offset multiplicity combine at the source-faithful scale: when $B$ dominates $M$, a constant fraction of $|Z||S|/M$ Z-stars survive with degree at least $H$. The theorem preserves shared Z multiplicity and does not include X/Y collision pruning or tensor realization.
-- source:
--   Dependent-weight averaging for the q=6 first hash in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 270--271

import Mathlib
import Theorems.Thm_mme_CW_q6_fixed_z_many_weights_above_half_mean
import Theorems.Thm_mme_CW_q6_z_hash_offset_label_card
import Theorems.Thm_mme_finset_incidence_double_count

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_many_retained_z_stars_from_fixed_fiber_moments
    {M n L G B H : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (Z : Finset (Fin (2 * (n + 1)) → Fin 3))
    (A : (Fin (2 * (n + 1)) → Fin 3) →
      Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (hz : ∀ z ∈ Z, ∀ e ∈ A z, e.1 2 = z)
    (hcard : ∀ z ∈ Z, (A z).card = B)
    (hB : 0 < B) (hH : 2 * M * H ≤ B)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range M) :
    let degree :
        (Fin (2 * (n + 1)) → Fin 3) →
          (Fin (2 * n + 2) → ZMod M) → ℕ := fun z w =>
      ((A z).attach.filter (fun e =>
        ∑ i,
          ((2 * ((e.1.1 0 i).val : ZMod M)) -
            (cwQ6CoupledZHashCode (e.1.1 2 i) : ZMod M)) * w i = 0)).card
    ∃ w : Fin (2 * n + 2) → ZMod M,
      ∃ b0 : ZMod M,
        B * S.card * Z.card ≤
          4 * M * (2 * M + B) *
            (Z.filter (fun z =>
              H ≤ degree z w ∧
                ∃ s ∈ S,
                  cwQ6DoubledZHash b0 w z =
                    2 * (s : ZMod M))).card := by
  sorry
